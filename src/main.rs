use std::fs;
use std::path::PathBuf;
use std::process;

use adaptrs::AdaptiveStrategy;
use adaptrs::parse_proof;
use adaptrs::verify_proof;

fn main() {
    // A simple CLI implementation
    // In a real application, this would use a proper CLI framework like clap
    
    let args: Vec<String> = std::env::args().collect();
    
    if args.len() < 2 {
        eprintln!("Usage: {} verify --file <proof_file> --strategy <reliability|minimal> [--verbose]", args[0]);
        process::exit(1);
    }
    
    match args[1].as_str() {
        "verify" => {
            // Parse command line arguments
            let mut file_path = None;
            let mut strategy = AdaptiveStrategy::Reliability;
            let mut verbose = false;
            
            let mut i = 2;
            while i < args.len() {
                match args[i].as_str() {
                    "--file" => {
                        if i + 1 < args.len() {
                            file_path = Some(PathBuf::from(&args[i + 1]));
                            i += 2;
                        } else {
                            eprintln!("Missing argument for --file");
                            process::exit(1);
                        }
                    },
                    "--strategy" => {
                        if i + 1 < args.len() {
                            match args[i + 1].as_str() {
                                "reliability" => strategy = AdaptiveStrategy::Reliability,
                                "minimal" => strategy = AdaptiveStrategy::MinimalAbnormality,
                                _ => {
                                    eprintln!("Invalid strategy: {}", args[i + 1]);
                                    process::exit(1);
                                }
                            }
                            i += 2;
                        } else {
                            eprintln!("Missing argument for --strategy");
                            process::exit(1);
                        }
                    },
                    "--verbose" => {
                        verbose = true;
                        i += 1;
                    },
                    _ => {
                        eprintln!("Unknown argument: {}", args[i]);
                        process::exit(1);
                    }
                }
            }
            
            // Check if file path is provided
            let file_path = match file_path {
                Some(path) => path,
                None => {
                    eprintln!("Missing required argument: --file");
                    process::exit(1);
                }
            };
            
            // Read proof file
            let proof_content = match fs::read_to_string(&file_path) {
                Ok(content) => content,
                Err(err) => {
                    eprintln!("Error reading file: {}", err);
                    process::exit(1);
                }
            };
            
            // Parse proof
            let mut proof = match parse_proof(&proof_content, strategy) {
                Ok(proof) => proof,
                Err(err) => {
                    eprintln!("Error parsing proof: {}", err);
                    process::exit(1);
                }
            };
            
            // Verify proof
            let result = verify_proof(&mut proof);
            
            // Display results
            if result.valid {
                println!("Proof is valid.");
            } else {
                println!("Proof is invalid.");
            }
            
            if verbose {
                println!("\nDetails:");
                for detail in &result.details {
                    println!("  {}", detail);
                }
            }
            
            // Display final proof with markings
            println!("\nFinal proof:");
            println!("{}", proof);
            
            if !result.valid {
                process::exit(1);
            }
        },
        _ => {
            eprintln!("Unknown command: {}", args[1]);
            eprintln!("Usage: {} verify --file <proof_file> --strategy <reliability|minimal> [--verbose]", args[0]);
            process::exit(1);
        }
    }
}