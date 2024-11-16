use std::alloc::{alloc, Layout};
use std::collections::{HashSet};
use std::ffi::CString;
use std::fs::File;
use std::io::{BufReader, BufRead};
use std::mem;
use std::time::{Duration, Instant};
use lazy_static::lazy_static;
use std::sync::Mutex;
use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::gates::random_access::RandomAccessGate;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::target::Target;
use plonky2_field::extension::Extendable;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use plonky2_util::log2_strict;
use libc::{c_char, c_void};
use jemallocator::Jemalloc;

#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;
static mut GLOBAL_BDD_size: usize = 0;
static mut GLOBAL_BDD_num: usize = 0;

lazy_static! {
    static ref GLOBAL_VEC: Mutex<Vec<u64>> = Mutex::new(Vec::new());
}

fn log2_judge(n: usize) -> bool {
    let res = n.trailing_zeros();
    n.wrapping_shr(res) == 1
}

fn random_access<F: RichField + Extendable<D>, const D: usize>(
    b: &mut CircuitBuilder<F, D>, 
    access_index: Target, 
    v: &Vec<Target>
) -> Target {
    // println!("begin RO\n");
    let vec_size = v.len();
    let bits = log2_strict(vec_size);
    debug_assert!(vec_size > 0);
    if vec_size == 1 {
        return v[0];
    }
    let claimed_element = b.add_virtual_target();

    let dummy_gate = RandomAccessGate::<F, D>::new_from_config(&b.config, bits);
    let (row, copy) = b.find_slot(dummy_gate, &[], &[]);

    v.iter().enumerate().for_each(|(i, &val)| {
        b.connect(val, Target::wire(row, dummy_gate.wire_list_item(i, copy)));
    });
    b.connect(
        access_index,
        Target::wire(row, dummy_gate.wire_access_index(copy)),
    );
    b.connect(
        claimed_element,
        Target::wire(row, dummy_gate.wire_claimed_element(copy)),
    );
    // println!("end RO\n");

    claimed_element
}

fn check_BDD<F: RichField + Extendable<D>, const D: usize>(
    BDD_buffer: &Vec<String>, 
    eval_buffer: &Vec<String>,
    builder: &mut CircuitBuilder<F, D>,
    pw: &mut PartialWitness<F>
) -> () {
    let mut BDD_index = 0;
    let mut eval_index = 0;
    while eval_index < eval_buffer.len() {
        if !eval_buffer[eval_index].starts_with("BDD") {println!("error\n");}
        while !BDD_buffer[BDD_index].starts_with("Bdd") {BDD_index += 1;}
        eval_index += 1;
        // println!("eval: {} BDD: {}\n", eval_index, BDD_index);

        // build vector of targets containing all the evaluations, which will be assigned dynamically
        let mut p_target: Vec<Target> = Vec::new();
        let bdd_size: Vec<&str> = BDD_buffer[BDD_index].split_whitespace().collect();
        BDD_index += 1;
        let BDD_size: usize = bdd_size[1].parse().unwrap();
        unsafe {GLOBAL_BDD_size = BDD_size;}
        // println!("BDD_size: {}\n", 3*BDD_size);
        for i in 0..3*BDD_size {
            let tmp_p= builder.add_virtual_target();
            if i < 5 {pw.set_target(tmp_p, F::ZERO);}
            if i == 5 {pw.set_target(tmp_p, F::ONE);}
            builder.register_public_input(tmp_p);
            p_target.push(tmp_p);
        }

        while !log2_judge(p_target.len()) {
            let tmp_p= builder.add_virtual_target();
            pw.set_target(tmp_p, F::ZERO);
            p_target.push(tmp_p);
        }

        // println!("p_target_size: {}\n", p_target.len());

        // build vector of targets containing all the assignments
        let mut sigma_target: Vec<Target> = Vec::new();
        let sigma_vec: Vec<&str> = eval_buffer[eval_index].split_whitespace().collect();
        for i in 0..sigma_vec.len() {
            let tmp_sigma = builder.add_virtual_target();
            builder.register_public_input(tmp_sigma);
            // println!("{}\n", sigma_vec[i]);
            let tmp_value: usize = sigma_vec[i].parse().unwrap();
            pw.set_target(tmp_sigma, F::from_canonical_usize(tmp_value));
            sigma_target.push(tmp_sigma);
        }

        eval_index += 1;

        if (eval_buffer[eval_index].contains("hash")) {
            let eval_tokens: Vec<&str> = eval_buffer[eval_index].split_whitespace().collect();
            let mut vec = GLOBAL_VEC.lock().unwrap();
            vec.push(eval_tokens[2].parse::<u64>().unwrap());
            vec.push(eval_tokens[3].parse::<u64>().unwrap());
            vec.push(eval_tokens[4].parse::<u64>().unwrap());
            for i in 2..BDD_size {
                // println!("update: {} {} {}\n", 3*i, 3*i+1, 3*i+2);
                pw.set_target(p_target[3*i], F::ZERO);
                pw.set_target(p_target[3*i+1], F::ZERO);
                pw.set_target(p_target[3*i+2], F::ZERO);
            }
            eval_index += 1;
            continue;
        }
        unsafe {GLOBAL_BDD_num += 1;}

        let mut p_target_set: HashSet<usize> = HashSet::new();

        while eval_index < eval_buffer.len() && !eval_buffer[eval_index].starts_with("BDD") {
            // println!("{}\n", eval_buffer[eval_index]);
            let eval_tokens: Vec<&str> = eval_buffer[eval_index].split_whitespace().collect();
            if (eval_tokens[0].starts_with("ret")) {
                eval_index += 1;
                let mut vec = GLOBAL_VEC.lock().unwrap();
                vec.push(eval_tokens[1].parse::<u64>().unwrap());
                vec.push(eval_tokens[2].parse::<u64>().unwrap());
                vec.push(eval_tokens[3].parse::<u64>().unwrap());
                continue;
            }
            let index: usize = eval_tokens[0].parse().unwrap();
            p_target_set.insert(index);
            let bdd_tokens: Vec<&str> = BDD_buffer[BDD_index + index].split_whitespace().collect();
            eval_index += 1;
            let mut normal_flag = 0;
            if eval_tokens[1].contains("N") {
                normal_flag = 1;

                // prove sigma[var] = p_var
                let p_var: u64 = eval_tokens[2].parse().unwrap();
                let var_index: usize = bdd_tokens[2].parse().unwrap();
                let p_var_target = builder.add_virtual_target();
                let var_index_target = builder.add_virtual_target();
                builder.register_public_input(p_var_target);
                builder.register_public_input(var_index_target);
                pw.set_target(p_var_target, F::from_canonical_u64(p_var));
                pw.set_target(var_index_target, F::from_canonical_usize(var_index));
                
                
                while !log2_judge(sigma_target.len()) {
                    let tmp_sigma= builder.add_virtual_target();
                    pw.set_target(tmp_sigma, F::ZERO);
                    sigma_target.push(tmp_sigma);
                }
                let var_out = random_access(builder, var_index_target, &sigma_target);
                builder.connect(var_out, p_var_target);
            }

            // update vector p
            let p_0: u64 = eval_tokens[3].parse().unwrap();
            let p_1: u64 = eval_tokens[4].parse().unwrap();
            let p_2: u64 = eval_tokens[5].parse().unwrap();

            // println!("update: p[{}]={} p[{}]={} p[{}]={}\n", 3*index, p_0, 3*index+1, p_1, 3*index+2, p_2);
            pw.set_target(p_target[3*index], F::from_noncanonical_u64(p_0));
            pw.set_target(p_target[3*index+1], F::from_noncanonical_u64(p_1));
            pw.set_target(p_target[3*index+2], F::from_noncanonical_u64(p_2));

            // prove p[low] = p_low
            let low_index: usize = eval_tokens[6].parse().unwrap();
            let p_low_0: u64 = eval_tokens[7].parse().unwrap();
            let p_low_1: u64 = eval_tokens[8].parse().unwrap();
            let p_low_2: u64 = eval_tokens[9].parse().unwrap();
            // println!("low_index: {}\n", low_index);
            // println!("p_low_0={} p_low_1={} p_low_2={}\n", p_low_0, p_low_1, p_low_2);
            let p_low_0_target = builder.add_virtual_target();
            let p_low_1_target = builder.add_virtual_target();
            let p_low_2_target = builder.add_virtual_target();
            let low_0_target = builder.add_virtual_target();
            let low_1_target = builder.add_virtual_target();
            let low_2_target = builder.add_virtual_target();
            builder.register_public_input(p_low_0_target);
            builder.register_public_input(p_low_1_target);
            builder.register_public_input(p_low_2_target);
            builder.register_public_input(low_0_target);
            builder.register_public_input(low_1_target);
            builder.register_public_input(low_2_target);
            pw.set_target(p_low_0_target, F::from_noncanonical_u64(p_low_0));
            pw.set_target(p_low_1_target, F::from_noncanonical_u64(p_low_1));
            pw.set_target(p_low_2_target, F::from_noncanonical_u64(p_low_2));
            pw.set_target(low_0_target, F::from_canonical_usize(3*low_index));
            pw.set_target(low_1_target, F::from_canonical_usize(3*low_index+1));
            pw.set_target(low_2_target, F::from_canonical_usize(3*low_index+2));
            if p_target_set.contains(&low_index) {
                let low_out_0 = random_access(builder, low_0_target, &p_target);
                let low_out_1 = random_access(builder, low_1_target, &p_target);
                let low_out_2 = random_access(builder, low_2_target, &p_target);
                builder.connect(low_out_0, p_low_0_target);
                builder.connect(low_out_1, p_low_1_target);
                builder.connect(low_out_2, p_low_2_target);
            }

            // prove p[high] = p_high
            let high_index: usize = eval_tokens[10].parse().unwrap();
            let p_high_0: u64 = eval_tokens[11].parse().unwrap();
            let p_high_1: u64 = eval_tokens[12].parse().unwrap();
            let p_high_2: u64 = eval_tokens[13].parse().unwrap();
            let p_high_0_target = builder.add_virtual_target();
            let p_high_1_target = builder.add_virtual_target();
            let p_high_2_target = builder.add_virtual_target();
            let high_0_target = builder.add_virtual_target();
            let high_1_target = builder.add_virtual_target();
            let high_2_target = builder.add_virtual_target();
            builder.register_public_input(p_high_0_target);
            builder.register_public_input(p_high_1_target);
            builder.register_public_input(p_high_2_target);
            builder.register_public_input(high_0_target);
            builder.register_public_input(high_1_target);
            builder.register_public_input(high_2_target);
            pw.set_target(p_high_0_target, F::from_noncanonical_u64(p_high_0));
            pw.set_target(p_high_1_target, F::from_noncanonical_u64(p_high_1));
            pw.set_target(p_high_2_target, F::from_noncanonical_u64(p_high_2));
            pw.set_target(high_0_target, F::from_canonical_usize(3*high_index));
            pw.set_target(high_1_target, F::from_canonical_usize(3*high_index+1));
            pw.set_target(high_2_target, F::from_canonical_usize(3*high_index+2));
            if p_target_set.contains(&high_index) {
                let high_out_0 = random_access(builder, high_0_target, &p_target);
                let high_out_1 = random_access(builder, high_1_target, &p_target);
                let high_out_2 = random_access(builder, high_2_target, &p_target);
                builder.connect(high_out_0, p_high_0_target);
                builder.connect(high_out_1, p_high_1_target);
                builder.connect(high_out_2, p_high_2_target);
            }



            let p_0_target = builder.add_virtual_target();
            let p_1_target = builder.add_virtual_target();
            let p_2_target = builder.add_virtual_target();
            pw.set_target(p_0_target, F::from_noncanonical_u64(p_0));
            pw.set_target(p_1_target, F::from_noncanonical_u64(p_1));
            pw.set_target(p_2_target, F::from_noncanonical_u64(p_2));

            if normal_flag == 1 {
                // prove p_ = (1 - p_var) * p_low + p_var * p_high
                let p_var: u64 = eval_tokens[2].parse().unwrap();
                if p_var == 0xffffffff00000000 {
                    let term1_0 = builder.neg(p_low_1_target);
                    let term1_1 = builder.sub(p_low_1_target, p_low_2_target);
                    let term1_2 = builder.add_virtual_target();
                    builder.generate_copy(p_low_2_target, term1_2);
                    let term2_0 = builder.add_virtual_target();
                    builder.generate_copy(p_high_1_target, term2_0);
                    let term2_1 = builder.add_virtual_target();
                    builder.generate_copy(p_high_2_target, term2_1);
                    let term2_2 = builder.add_virtual_target();
                    pw.set_target(term2_2, F::ZERO);
                    let term_0 = builder.add(term1_0, term2_0);
                    let term_1 = builder.add(term1_1, term2_1);
                    let term_2 = builder.add(term1_2, term2_2);
                    let p_0_target = builder.add_virtual_target();
                    let p_1_target = builder.add_virtual_target();
                    let p_2_target = builder.add_virtual_target();
                    pw.set_target(p_0_target, F::from_noncanonical_u64(p_0));
                    pw.set_target(p_1_target, F::from_noncanonical_u64(p_1));
                    pw.set_target(p_2_target, F::from_noncanonical_u64(p_2));
                    builder.connect(p_0_target, term_0);
                    builder.connect(p_1_target, term_1);
                    builder.connect(p_2_target, term_2);
                } else {
                    // println!("p: {} {} {}, var: {}, p_low: {} {} {}, p_high: {} {} {}\n", p_0, p_1, p_2, p_var, p_low_0, p_low_1, p_low_2, p_high_0, p_high_1, p_high_2);
                    let p_var_target = builder.add_virtual_target();
                    builder.register_public_input(p_var_target);
                    pw.set_target(p_var_target, F::from_canonical_u64(p_var));
                    let const_one = builder.constant(F::ONE);
                    let oneminus_p_var = builder.sub(const_one, p_var_target);
                    let term1_0 = builder.mul(oneminus_p_var, p_low_0_target);
                    let term1_1 = builder.mul(oneminus_p_var, p_low_1_target);
                    let term1_2 = builder.mul(oneminus_p_var, p_low_2_target);
                    let term2_0 = builder.mul(p_var_target, p_high_0_target);
                    let term2_1 = builder.mul(p_var_target, p_high_1_target);
                    let term2_2 = builder.mul(p_var_target, p_high_2_target);
                    let term_0 = builder.add(term1_0, term2_0);
                    let term_1 = builder.add(term1_1, term2_1);
                    let term_2 = builder.add(term1_2, term2_2);
                    builder.connect(p_0_target, term_0);
                    builder.connect(p_1_target, term_1);
                    builder.connect(p_2_target, term_2);
                }
            } else {
                // prove p_ = p_low binop p_high
                let binop: usize = eval_tokens[2].parse().unwrap();
                let constzero = builder.constant(F::ZERO);
                let constone = builder.constant(F::ONE);
                let mult0_a = builder.mul(p_low_1_target, p_high_1_target);
                let mult0_b = builder.mul(p_low_0_target, p_high_2_target);
                let mult0_c = builder.mul(p_low_2_target, p_high_0_target);
                let mult0_tmp = builder.add(mult0_a, mult0_b);
                let mult0 = builder.add(mult0_tmp, mult0_c);
                let mult1_a = builder.mul(p_high_1_target, p_low_2_target);
                let mult1_b = builder.mul(p_high_2_target, p_low_1_target);
                let mult1 = builder.add(mult1_a, mult1_b);
                let mult2 = builder.mul(p_low_2_target, p_high_2_target);
                match binop {
                    0 => {
                        builder.connect(constzero, p_0_target);
                        builder.connect(constzero, p_1_target);
                        builder.connect(constzero, p_2_target);
                    },
                    1 => {
                        let tmp0 = builder.sub(constone, p_high_2_target);
                        let tmp1 = builder.sub(tmp0, p_low_2_target);
                        let tmp2 = builder.add(tmp1, mult2);
                        builder.connect(tmp2, p_2_target);
                        let tmp3 = builder.sub(mult1, p_high_1_target);
                        let tmp4 = builder.sub(tmp3, p_low_1_target);
                        builder.connect(tmp4, p_1_target);
                        let tmp5 = builder.sub(mult0, p_high_0_target);
                        let tmp6 = builder.sub(tmp5, p_low_0_target);
                        builder.connect(tmp6, p_0_target);
                    },
                    2 => {
                        let tmp0 = builder.sub(p_low_0_target, mult0);
                        let tmp1 = builder.sub(p_low_1_target, mult1);
                        let tmp2 = builder.sub(p_low_2_target, mult2);
                        builder.connect(tmp0, p_0_target);
                        builder.connect(tmp1, p_1_target);
                        builder.connect(tmp2, p_2_target);
                    },
                    3 => {
                        let tmp0 = builder.neg(p_high_0_target);
                        let tmp1 = builder.neg(p_high_1_target);
                        let tmp2 = builder.sub(constone, p_high_2_target);
                        builder.connect(tmp0, p_0_target);
                        builder.connect(tmp1, p_1_target);
                        builder.connect(tmp2, p_2_target);
                    },
                    4 => {
                        let tmp0 = builder.sub(p_high_0_target, mult0);
                        let tmp1 = builder.sub(p_high_1_target, mult1);
                        let tmp2 = builder.sub(p_high_2_target, mult2);
                        builder.connect(tmp0, p_0_target);
                        builder.connect(tmp1, p_1_target);
                        builder.connect(tmp2, p_2_target);
                    },
                    5 => {
                        let tmp0 = builder.neg(p_low_0_target);
                        let tmp1 = builder.neg(p_low_1_target);
                        let tmp2 = builder.sub(constone, p_low_2_target);
                        builder.connect(tmp0, p_0_target);
                        builder.connect(tmp1, p_1_target);
                        builder.connect(tmp2, p_2_target);
                    },
                    6 => {
                        let tmp0 = builder.add(p_low_0_target, p_high_0_target);
                        let tmp1 = builder.add(p_low_1_target, p_high_1_target);
                        let tmp2 = builder.add(p_low_2_target, p_high_2_target);
                        let tmp3 = builder.sub(tmp0, mult0);
                        let tmp4 = builder.sub(tmp1, mult1);
                        let tmp5 = builder.sub(tmp2, mult2);
                        let tmp6 = builder.sub(tmp3, mult0);
                        let tmp7 = builder.sub(tmp4, mult1);
                        let tmp8 = builder.sub(tmp5, mult2);
                        builder.connect(tmp6, p_0_target);
                        builder.connect(tmp7, p_1_target);
                        builder.connect(tmp8, p_2_target);
                    },
                    7 => {
                        let tmp0 = builder.neg(mult0);
                        let tmp1 = builder.neg(mult1);
                        let tmp2 = builder.sub(constone, mult2);
                        builder.connect(tmp0, p_0_target);
                        builder.connect(tmp1, p_1_target);
                        builder.connect(tmp2, p_2_target);
                    },
                    8 => {
                        builder.connect(p_0_target, mult0);
                        builder.connect(p_1_target, mult1);
                        builder.connect(p_2_target, mult2);
                    }
                    9 => {
                        let tmp0 = builder.sub(constone, p_high_2_target);
                        let tmp1 = builder.sub(tmp0, p_low_2_target);
                        let tmp2 = builder.add(tmp1, mult2);
                        let tmp7 = builder.add(tmp2, mult2);
                        builder.connect(tmp7, p_2_target);
                        let tmp3 = builder.sub(mult1, p_high_1_target);
                        let tmp4 = builder.sub(tmp3, p_low_1_target);
                        let tmp8 = builder.add(tmp4, mult1);
                        builder.connect(tmp8, p_1_target);
                        let tmp5 = builder.sub(mult0, p_high_0_target);
                        let tmp6 = builder.sub(tmp5, p_low_0_target);
                        let tmp9 = builder.add(tmp6, mult0);
                        builder.connect(tmp9, p_0_target);
                    },
                    10 => {
                        builder.connect(p_0_target, p_low_0_target);
                        builder.connect(p_1_target, p_low_1_target);
                        builder.connect(p_2_target, p_low_2_target);
                    },
                    11 => {
                        let tmp0 = builder.sub(constone, p_high_2_target);
                        let tmp2 = builder.add(tmp0, mult2);
                        builder.connect(tmp2, p_2_target);
                        let tmp3 = builder.sub(mult1, p_high_1_target);
                        builder.connect(tmp3, p_1_target);
                        let tmp5 = builder.sub(mult0, p_high_0_target);
                        builder.connect(tmp5, p_0_target);
                    },
                    12 => {
                        builder.connect(p_0_target, p_high_0_target);
                        builder.connect(p_1_target, p_high_1_target);
                        builder.connect(p_2_target, p_high_2_target);
                    },
                    13 => {
                        let tmp0 = builder.sub(constone, p_low_2_target);
                        let tmp2 = builder.add(tmp0, mult2);
                        builder.connect(tmp2, p_2_target);
                        let tmp3 = builder.sub(mult1, p_low_1_target);
                        builder.connect(tmp3, p_1_target);
                        let tmp5 = builder.sub(mult0, p_low_0_target);
                        builder.connect(tmp5, p_0_target);
                    },
                    14 => {
                        let tmp0 = builder.add(p_low_0_target, p_high_0_target);
                        let tmp1 = builder.add(p_low_1_target, p_high_1_target);
                        let tmp2 = builder.add(p_low_2_target, p_high_2_target);
                        let tmp3 = builder.sub(tmp0, mult0);
                        let tmp4 = builder.sub(tmp1, mult1);
                        let tmp5 = builder.sub(tmp2, mult2);
                        builder.connect(tmp3, p_0_target);
                        builder.connect(tmp4, p_1_target);
                        builder.connect(tmp5, p_2_target);
                    },
                    15 => {
                        builder.connect(constone, p_0_target);
                        builder.connect(constone, p_1_target);
                        builder.connect(constone, p_2_target);
                    },
                    _ => println!("Error.\n"),
                }

            }
        }

        for i in 2..BDD_size {
            if !p_target_set.contains(&i) {
                // println!("update: {} {} {}\n", 3*i, 3*i+1, 3*i+2);
                pw.set_target(p_target[3*i], F::from_noncanonical_u64(0));
                pw.set_target(p_target[3*i+1], F::from_noncanonical_u64(0));
                pw.set_target(p_target[3*i+2], F::from_noncanonical_u64(0));
            }
        }
    }
}

fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let mut pw = PartialWitness::new();

    let str_vec = vec![
        "test/BEQ-N-3.qdimacs_", // 4300
        "test/CR-N-3.qdimacs_", // 1100 14509MB node:256 #135
        "test/CR-N-4.qdimacs_", // 2200
        "test/CR-N-5.qdimacs_", // 4300
        "test/EQ-N-3.qdimacs_", // 1200 3756MB node:104 #104
        "test/EQ-N-4.qdimacs_", // 2300
        "test/EQ-N-5.qdimacs_", // 2300
        "test/KBKF_LD-N-3.qdimacs_", // 1200 33476MB node:328 #241
        "test/KBKF_LD-N-4.qdimacs_", // 4200
        "test/KBKF_QU-N-3.qdimacs_", // 2300
        "test/KBKF_QU-N-4.qdimacs_", // 4200
        "test/KBKF-N-3.qdimacs_", // 2300
        "test/KBKF-N-4.qdimacs_", // 600 4151MB node:165 #224
        "test/KBKF-N-5.qdimacs_", // 1200 23129MB node:222 #312
        "test/KBKF-N-8.qdimacs_", // 2100
        "test/KBKF-N-10.qdimacs_", // 2100
        "test/LONSING-N-3.qdimacs_", // 1100 21944MB node:265 #211
        "test/LONSING-N-4.qdimacs_", // 2300
        "test/LQ_PARITY-N-4.qdimacs_", // 1200 22099MB node:285 #182
        "test/LQ_PARITY-N-5.qdimacs_", // 2300
        "test/LQ_PARITY-N-8.qdimacs_", // 2300
        "test/PARITY-N-3.qdimacs_", // 600 1076MB node:88 #76
        "test/PARITY-N-4.qdimacs_", // 600 2246MB node:130 #101
        "test/PARITY-N-5.qdimacs_", // 1300 7533MB node:178 #66
        "test/PARITY-N-8.qdimacs_", // 2300
        "test/PARITY-N-10.qdimacs_", // 2300
        "test/PARITY-N-15.qdimacs_", // 4300
        "test/QU_PARITY-N-3.qdimacs_", // 1200 22275MB node:292 #156
        "test/QU_PARITY-N-4.qdimacs_", // 2300
        "test/QU_PARITY-N-5.qdimacs_" // 2300
    ];

    let para_vec = vec![4300, 1100, 2200, 4300, 1200, 2300, 2300, 1200, 
                                  4200, 2300, 4200, 2300, 600, 1200, 2100, 2100,
                                  1100, 2300, 1200, 2300, 2300, 600, 600, 1300,
                                  2300, 2300, 4300, 1200, 2300, 2300];
                                  

    let str = "test/CR-N-4.qdimacs_";
    let BDD_str = format!("{}{}", str, "BDD.txt");
    let eval_str = format!("{}{}", str, "eval.txt");
    let CP_str = format!("{}{}", str, "CP.txt");
    let BDD_file = File::open(BDD_str)?;
    let eval_file = File::open(eval_str)?;
    let CP_file = File::open(CP_str)?;
    let BDD_reader = BufReader::new(BDD_file);
    let BDD_buffer: Vec<_> = BDD_reader.lines().collect::<Result<_, _>>()?;
    let eval_reader = BufReader::new(eval_file);
    let eval_buffer: Vec<_> = eval_reader.lines().collect::<Result<_, _>>()?;
    let CP_reader = BufReader::new(CP_file);
    let mut CP_buffer: Vec<_> = CP_reader.lines().collect::<Result<_, _>>()?;
    let mut CP_index = 0;

    check_BDD::<F, D>(&BDD_buffer, &eval_buffer, &mut builder, &mut pw);
    let mut vec_target: Vec<Target> = Vec::new();
    let mut vec = GLOBAL_VEC.lock().unwrap();
    // println!("\nvec: ");
    for i in 0..vec.len() {
        let tmp = builder.add_virtual_target();
        builder.register_public_input(tmp);
        let tmp_value: u64 = vec[i];
        // println!(" {} ", tmp_value);
        pw.set_target(tmp, F::from_canonical_u64(tmp_value));
        vec_target.push(tmp);
    }
    while !log2_judge(vec_target.len()) {
        let tmp= builder.add_virtual_target();
        pw.set_target(tmp, F::ZERO);
        vec_target.push(tmp);
    }
    while CP_index < CP_buffer.len() {
        let line = &CP_buffer[CP_index];
        if line.starts_with("eval") {
            CP_index += 1;
        } else if line.starts_with("merge") {
            while !CP_buffer[CP_index].starts_with("end") {
                CP_index += 1;
            }
            CP_index += 1;
        } else if line.starts_with("binop") {
            CP_index += 3;
        } else if line.starts_with("degree") {
            CP_index += 3;
        } else if line.starts_with("leaf") {
            let tokens: Vec<&str> = line.split_whitespace().collect();
            let eval: u64 = tokens[1].parse()?;
            let p_val: u64 = tokens[2].parse()?;
            let eval_ = builder.add_virtual_target();
            let p_val_ = builder.add_virtual_target();
            builder.register_public_input(eval_);
            builder.register_public_input(p_val_);
            pw.set_target(eval_, F::from_noncanonical_u64(eval));
            pw.set_target(p_val_, F::from_noncanonical_u64(p_val));
            builder.connect(eval_, p_val_);
            CP_index += 1;
        }
    }
    // println!("out\n");

    let data = builder.build::<C>();
    let constraints: usize = data.common.gates.iter().map(|gate| gate.0.num_constraints()).sum();
    let prove_start = Instant::now();
    let proof = data.prove(pw)?;
    let prove_duration = prove_start.elapsed();
    println!("Proving time elapsed: {:?}", prove_duration);
    let letters = CString::new("stats.resident").unwrap();
    let p_letters: *const c_char = letters.as_ptr() as *const c_char;
    let layout = Layout::new::<u64>();
    let ptr = unsafe { alloc(layout) as *mut c_void };
    let mut len: usize = mem::size_of::<u64>();
    let mut p_len: *mut usize = &mut len;
    if unsafe { jemalloc_sys::mallctl(p_letters, ptr, p_len, std::ptr::null_mut(), 0) } == 0 {
        
    }
    unsafe {
        // Cast the void pointer to a pointer to u64 and write a value
        let u64_ptr = ptr as *mut u64;

        // Print the value stored in the pointer
        println!("Value at allocated memory: {} MB, #BDD nodes: {}, #BDD proved: {}", *u64_ptr/1024/1024, GLOBAL_BDD_size, GLOBAL_BDD_num);
    }
    
    println!("Constraints number: {}", constraints);
    println!("Size of proof: {}", mem::size_of_val(&proof));
    let verify_start = Instant::now();
    let ret = data.verify(proof);
    let verify_duration = verify_start.elapsed();
    println!("Verification time elapsed: {:?}", verify_duration);
    ret
}

// BDD size (#node) // #BDD // circuit width // memory resident // P time   // V time
// 165              // 224  // 600           // 4.05GB          // 416.74s  // 1.67s
// 88               // 76   // 600           // 1.05GB          // 103.21s  // 666.69ms 392B
// 130              // 101  // 600           // 2.19GB          // 210.57s  // 931.47ms
// 265              // 211  // 1100          // 21.43GB         // 1347.44s // 3.43s
// 222              // 312  // 1200          // 22.59GB         // 1444.86s // 2.59s
// 256              // 135  // 1300          // 14.17GB         // 741.46s  // 2.08s
// 104              // 104  // 1300          // 3.67GB          // 201.81s  // 1.13s
// 285              // 182  // 1300          // 21.58GB         // 1449.02s // 2.24s
// 178              // 66   // 1300          // 7.36GB          // 426.33s  // 1.26s
// 292              // 156  // 1400          // 21.75GB         // 1678.77s // 2.26s
