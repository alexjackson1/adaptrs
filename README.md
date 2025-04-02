# Adaptrs: Adaptive Logic Proof Verifier

Adaptrs is a Rust implementation of a proof verifier for adaptive logic systems. Adaptive logics are formal frameworks for nonmonotonic reasoning, where conclusions can be withdrawn when new information is added.

## Features

- Formula representation with propositional variables and operators (¬, ∧, ∨, →, ↔)
- Proof verification with line-by-line justification checking
- Support for both reliability and minimal abnormality strategies
- Tracking of abnormality conditions (disjunctive syllogism violations and contradictions)
- CLI interface for verifying proofs from files

## Installation

With Rust and Cargo installed:

```bash
git clone https://github.com/your-username/adaptrs.git
cd adaptrs
cargo build --release
```

## Usage

### CLI

```bash
# Verify a proof file with the reliability strategy
cargo run -- verify --file examples/simple_proof.txt --strategy reliability --verbose

# Verify a proof file with the minimal abnormality strategy
cargo run -- verify --file examples/simple_proof.txt --strategy minimal --verbose
```

### Library

```rust
use adaptrs::formula::Formula;
use adaptrs::proof::{Proof, Rule};
use adaptrs::strategy::AdaptiveStrategy;
use adaptrs::verifier::verify_proof;
use std::collections::HashSet;

// Create a new proof with reliability strategy
let mut proof = Proof::new(AdaptiveStrategy::Reliability);

// Add premises and derived lines
let p = Formula::var("P");
let q = Formula::var("Q");
proof.add_premise(p.clone());
proof.add_premise(q.clone());
proof.add_line(
    Formula::conj(p, q),
    Rule::AndIntro,
    vec![1, 2],
    HashSet::new()
);

// Verify the proof
let result = verify_proof(&mut proof);
println!("Proof is valid: {}", result.valid);
```

## Proof Format

Proofs are specified in a text file with the following format:

```
# Comments start with #
1. Formula                   PREM
2. Formula                   PREM
3. Formula                   1,2 Rule {Abnormality conditions}
```

Where:
- Line numbers are sequential
- Formulas use standard logical notation (P, Q, ¬, ∧, ∨, →, ↔)
- Justifications can be PREM or refer to previous lines with a rule
- Abnormality conditions are optional and enclosed in curly braces

## Supported Rules

- Premise (PREM)
- Conjunction introduction (∧I)
- Conjunction elimination (∧E1, ∧E2)
- Disjunction introduction (∨I1, ∨I2)
- Modus ponens (MP)
- Modus tollens (MT)
- Disjunctive syllogism (DS)
- Ex falso quodlibet (EFQ)

## License

[MIT](LICENSE)