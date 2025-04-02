# Adaptive Logic Proof Verifier

A Rust implementation of a proof verifier for adaptive logics, a formal framework for nonmonotonic reasoning where conclusions can be withdrawn when new information is added.

## Overview

Adaptive logics provide a formal framework for nonmonotonic reasoning, where conclusions that are derived at one stage may be withdrawn at a later stage when more premises are added. This proof verifier implements:

1. A lower limit logic (classical propositional logic without disjunctive syllogism and ex falso quodlibet)
2. An upper limit logic (full classical propositional logic)
3. Abnormality tracking for inconsistencies
4. Two adaptive strategies:
   - Reliability strategy
   - Minimal abnormality strategy

## Features

- Parse and verify proofs in adaptive logic
- Robust formula parsing with nom parser combinators
- Identify abnormalities (contradictions, disjunctive syllogism violations)
- Apply adaptive strategies to mark invalid lines
- Provide detailed verification results
- Support for various proof rule notations

## Installation

Clone the repository and build using Cargo:

```bash
git clone https://github.com/yourusername/adaptrs.git
cd adaptrs
cargo build --release
```

## Usage

Verify a proof file using the reliability strategy:

```bash
adaptrs verify --file examples/simple_proof.txt --strategy reliability
```

For detailed verification information:

```bash
adaptrs verify --file examples/simple_proof.txt --strategy reliability --verbose
```

## Proof File Format

Proof files use a simple syntax:

```
1. P ∨ Q                         PREM
2. ¬P                           PREM
3. Q                            1,2 DS {(P ∨ Q) ∧ ¬P ∧ ¬Q}
```

Each line contains:
1. Line number
2. Formula
3. Justification (rule and reference lines)
4. Conditions (abnormalities) in curly braces for conditional derivations

## Adaptive Logic Rules

- **PREM**: Premise introduction
- **Unconditional Rules**:
  - ∧I/AND-I: Conjunction Introduction
  - ∧E1/AND-E1: Conjunction Elimination (first conjunct)
  - ∧E2/AND-E2: Conjunction Elimination (second conjunct)
  - ∨I1/OR-I1: Disjunction Introduction (from first disjunct)
  - ∨I2/OR-I2: Disjunction Introduction (from second disjunct)
  - MP: Modus Ponens
  - MT: Modus Tollens
- **Conditional Rules**:
  - DS: Disjunctive Syllogism
  - EFQ: Ex Falso Quodlibet

## Formula Syntax

The parser supports a wide range of propositional logic formula notations:

### Variables
- Single characters: `P`, `Q`, `R`
- Multi-character names: `Prop1`, `Assert`, `P_1`

### Logical Operators
- Negation: `¬P`, `~P`, `!P`
- Conjunction: `P ∧ Q`, `P & Q`, `P && Q`, `P and Q`
- Disjunction: `P ∨ Q`, `P | Q`, `P || Q`, `P or Q`
- Implication: `P → Q`, `P -> Q`, `P implies Q`
- Biconditional: `P ↔ Q`, `P <-> Q`, `P iff Q`

### Operator Precedence
The parser correctly handles operator precedence:
1. Parentheses: `(P ∧ Q)`
2. Negation: `¬P`
3. Conjunction: `P ∧ Q`
4. Disjunction: `P ∨ Q`
5. Implication: `P → Q`
6. Biconditional: `P ↔ Q`

For example, `P ∧ Q ∨ R` is parsed as `(P ∧ Q) ∨ R` due to conjunction having higher precedence than disjunction.

### Whitespace Flexibility
The parser handles various spacing patterns:
- Standard spacing: `P ∧ Q`
- No spaces: `P∧Q`
- Extra spaces: `P   ∧   Q`

## License

This project is licensed under the MIT License - see the LICENSE file for details.