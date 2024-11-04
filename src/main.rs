use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;

use simfony::{Arguments, CompiledProgram};
use std::env;

// Directly returning Result<(), String> prints the error using Debug
// Add indirection via run() to print errors using Display
fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

#[cfg(feature = "serde")]
fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("Usage: {} PROGRAM_FILE [WITNESS_FILE]", args[0]);
        println!(
            "Compile the given Simfony program and print the resulting Simplicity base64 string."
        );
        println!("If a Simfony witness is provided, then use it to satisfy the program.");
        return Ok(());
    }

    let prog_file = &args[1];
    let prog_path = std::path::Path::new(prog_file);
    let prog_text = std::fs::read_to_string(prog_path).map_err(|e| e.to_string())?;
    let compiled = CompiledProgram::new(prog_text, Arguments::default())?;

    if args.len() >= 3 {
        let wit_file = &args[2];
        let wit_path = std::path::Path::new(wit_file);
        let wit_text = std::fs::read_to_string(wit_path).map_err(|e| e.to_string())?;
        let witness = serde_json::from_str::<simfony::WitnessValues>(&wit_text).unwrap();

        let satisfied = compiled.satisfy(witness)?;
        let (program_bytes, witness_bytes) = satisfied.redeem().encode_to_vec();
        println!(
            "Program:\n{}",
            Base64Display::new(&program_bytes, &STANDARD)
        );
        println!(
            "Witness:\n{}",
            Base64Display::new(&witness_bytes, &STANDARD)
        );
    } else {
        let program_bytes = compiled.commit().encode_to_vec();
        println!(
            "Program:\n{}",
            Base64Display::new(&program_bytes, &STANDARD)
        );
    }

    Ok(())
}

#[cfg(not(feature = "serde"))]
fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("Usage: {} PROGRAM_FILE", args[0]);
        println!(
            "Compile the given Simfony program and print the resulting Simplicity base64 string."
        );
        return Ok(());
    }

    let prog_file = &args[1];
    let prog_path = std::path::Path::new(prog_file);
    let prog_text = std::fs::read_to_string(prog_path).map_err(|e| e.to_string())?;
    let compiled = CompiledProgram::new(prog_text, Arguments::default())?;

    let program_bytes = compiled.commit().encode_to_vec();
    println!(
        "Program:\n{}",
        Base64Display::new(&program_bytes, &STANDARD)
    );

    Ok(())
}
