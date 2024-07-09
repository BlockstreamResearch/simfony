use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;

use simfony::{compile, satisfy};

use std::env;

// Directly returning Result<(), String> prints the error using Debug
// Add indirection via run() to print errors using Display
fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    // Get the command-line arguments as a Vec<String>.
    let args: Vec<String> = env::args().collect();

    // Check if at least two arguments are provided.
    if args.len() < 2 {
        println!("Usage: {} <prog.simpl> [sig.wit (optional)]", args[0]);
        println!("If no witness file is provided, the program will be compiled and printed.");
        println!("If a witness file is provided, the program will be satisfied and printed.");
        return Ok(());
    }

    // Extract the first argument (arg1).
    let prog_file = &args[1];
    let prog_path = std::path::Path::new(prog_file);

    // Check if a second argument (arg2) is provided.
    if args.len() >= 3 {
        // TODO: Re-enable witness file parsing
        println!(
            "Warning: Witness expressions are temporarily disabled. Skipping the witness file..."
        );
        // let witness_file = &args[2];
        // let wit_path = std::path::Path::new(witness_file);
        let res = satisfy(prog_path)?;
        let redeem_bytes = res.encode_to_vec();
        println!("{}", Base64Display::new(&redeem_bytes, &STANDARD));
    } else {
        // No second argument is provided. Just compile the program.
        let prog = compile(prog_path)?;
        let res = prog.encode_to_vec();
        println!("{}", Base64Display::new(&res, &STANDARD));
    }

    Ok(())
}
