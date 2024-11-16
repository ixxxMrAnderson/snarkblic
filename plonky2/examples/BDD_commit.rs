use std::fs::File;
use std::io::{BufReader, BufRead};
use std::mem::size_of_val;
use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::{CircuitConfig, CircuitData};
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

fn main() -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let mut pw = PartialWitness::new();

    let file = File::open("BDD.txt")?;
    let reader = BufReader::new(file);
    let mut lines_iter = reader.lines();
    let mut BDD_size: usize = 0;
    while let Some(line_result) = lines_iter.next() {
        let mut line = line_result?;
        if line.starts_with("Bdd_store") {
            let tokens: Vec<&str> = line.split_whitespace().collect();
            BDD_size = tokens[1].parse()?;
        } else {
            let tokens: Vec<&str> = line.split_whitespace().collect();
            let index: usize = tokens[0].parse()?;
            if index < 2 {continue;}
            let var: usize = tokens[2].parse()?;
            let low_child: usize = tokens[3].parse()?;
            let high_child: usize = tokens[4].parse()?;
            let target_index = builder.add_virtual_target();
            let target_var = builder.add_virtual_target();
            let target_low = builder.add_virtual_target();
            let target_high = builder.add_virtual_target();
            builder.register_public_input(target_index);
            builder.register_public_input(target_var);
            builder.register_public_input(target_low);
            builder.register_public_input(target_high);
            pw.set_target(target_index, F::from_canonical_usize(index));
            pw.set_target(target_var, F::from_canonical_usize(var));
            pw.set_target(target_low, F::from_canonical_usize(low_child));
            pw.set_target(target_high, F::from_canonical_usize(high_child));
            let sub_low = builder.sub(target_index, target_low);
            let sub_high = builder.sub(target_index, target_high);
            builder.range_check(target_var, BDD_size);
            builder.range_check(sub_low, BDD_size);
            builder.range_check(sub_high, BDD_size);
        }
    }

    let data = builder.build::<C>();
    println!("{}\n", size_of_val(&data));
    let proof = data.prove(pw)?;
    let public_inputs_hash = proof.get_public_inputs_hash();

    //  3. generate random challenge
    let challenge = proof.get_challenges(public_inputs_hash, &data.verifier_only.circuit_digest, &data.common); // WRITE CHALLENGE
    
    data.verify(proof)
}