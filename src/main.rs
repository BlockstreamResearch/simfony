use std::env;
use std::sync::Arc;

use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;

use s_lang::{compile, satisfy};

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
    let program_file = &args[1];
    let program_path = std::path::Path::new(program_file);
    let program_str = std::fs::read_to_string(program_path)
        .map(Arc::<str>::from)
        .unwrap();

    // Check if a second argument (arg2) is provided.
    if args.len() >= 3 {
        let witness_file = &args[2];
        let wit_path = std::path::Path::new(witness_file);
        let res = satisfy(program_str, wit_path).unwrap();
        let redeem_bytes = res.encode_to_vec();
        println!("{}", Base64Display::new(&redeem_bytes, &STANDARD));
    } else {
        // No second argument is provided. Just compile the program.
        let prog = compile(program_str)?;
        let res = prog.encode_to_vec();
        println!("{}", Base64Display::new(&res, &STANDARD));
    }

    Ok(())
}
