use std::fs;
use std::path::PathBuf;
use std::process;

use adaptrs::parse_proof;
use adaptrs::verify_proof;
use adaptrs::AdaptiveStrategy;
use clap::{Parser, Subcommand, ValueEnum};

#[derive(Parser)]
#[command(
    name = "adaptrs",
    about = "An adaptive logic proof verifier",
    version,
    author
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Verify an adaptive logic proof
    Verify(VerifyArgs),
}

#[derive(Parser)]
struct VerifyArgs {
    /// Path to the proof file
    #[arg(short, long, value_name = "FILE")]
    file: PathBuf,

    /// Strategy for handling abnormalities
    #[arg(short, long, value_enum, default_value_t = Strategy::Reliability)]
    strategy: Strategy,

    /// Enable verbose output
    #[arg(short, long)]
    verbose: bool,
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum Strategy {
    /// Reliability strategy
    Reliability,
    /// Minimal abnormality strategy
    Minimal,
}

impl From<Strategy> for AdaptiveStrategy {
    fn from(strategy: Strategy) -> Self {
        match strategy {
            Strategy::Reliability => AdaptiveStrategy::Reliability,
            Strategy::Minimal => AdaptiveStrategy::MinimalAbnormality,
        }
    }
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Verify(args) => {
            // Read proof file
            let proof_content = match fs::read_to_string(&args.file) {
                Ok(content) => content,
                Err(err) => {
                    eprintln!("Error reading file: {}", err);
                    process::exit(1);
                }
            };

            // Parse proof
            let strategy: AdaptiveStrategy = args.strategy.into();
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

            if args.verbose {
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
        }
    }
}
