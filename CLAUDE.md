# Adaptive Logic Proof Verifier - Implementation Guide

## Project Overview

This project implements a proof verifier for an adaptive logic system in Rust. Adaptive logics are formal frameworks for nonmonotonic reasoning, where conclusions can be withdrawn when new information is added.

The specific adaptive logic system has:
- A lower limit logic: classical propositional logic without disjunctive syllogism and ex falso quodlibet
- An upper limit logic: full classical propositional logic
- Defined abnormalities: formulas that behave differently between the lower and upper limit logics
- Adaptive strategies for handling abnormalities: reliability or minimal abnormality

## Core Components

### 1. Formula Representation

Implement propositional formulas with the following operators:
- Propositional variables (e.g., P, Q, R)
- Negation (¬)
- Conjunction (∧)
- Disjunction (∨)
- Implication (→)
- Biconditional (↔)

```rust
enum Formula {
    Var(String),
    Neg(Box<Formula>),
    Conj(Box<Formula>, Box<Formula>),
    Disj(Box<Formula>, Box<Formula>),
    Impl(Box<Formula>, Box<Formula>),
    Bicon(Box<Formula>, Box<Formula>),
}
```

### 2. Proof Representation

A proof consists of numbered lines, where each line contains:
- A formula
- A justification (premise or rule application with line references)
- A set of abnormality conditions (if derived conditionally)
- A marking status (marked/unmarked)

```rust
struct ProofLine {
    line_number: usize,
    formula: Formula,
    justification: Justification,
    conditions: HashSet<Abnormality>,
    marked: bool,
}

enum Justification {
    Premise,
    RuleApplication {
        rule: Rule,
        from_lines: Vec<usize>,
    },
}

struct Proof {
    lines: Vec<ProofLine>,
    strategy: AdaptiveStrategy,
}
```

### 3. Abnormality Definition

Two types of abnormalities:
- Disjunctive syllogism violations: (A ∨ B) ∧ ¬A ∧ ¬B
- Contradictions: A ∧ ¬A

```rust
enum Abnormality {
    DisjunctiveSyllogismViolation(Formula, Formula),  // For (A ∨ B) ∧ ¬A ∧ ¬B
    Contradiction(Formula),  // For A ∧ ¬A
}
```

### 4. Proof Rules

Implement three types of rules:
- PREM: Premise introduction
- RU: Unconditional inference rules from lower limit logic
- RC: Conditional inference rules that rely on abnormality assumptions

```rust
enum Rule {
    Prem,
    // Unconditional Rules (Lower Limit Logic)
    AndIntro,
    AndElim1,
    AndElim2,
    OrIntro1,
    OrIntro2,
    // ... other rules from lower limit logic
    
    // Conditional Rules
    DisjSyll,  // (A ∨ B) ∧ ¬A ⊢ B
    ExFalso,   // (A ∧ ¬A) ⊢ B
}
```

### 5. Adaptive Strategies

Implement two strategies:
- Reliability strategy: Mark lines that depend on formulas that are shown to be unreliable
- Minimal abnormality strategy: Consider all minimal sets of abnormalities and mark lines accordingly

```rust
enum AdaptiveStrategy {
    Reliability,
    MinimalAbnormality,
}
```

## Module Structure

1. **formula.rs**: Define the Formula enum and related operations
2. **parser.rs**: Parse input strings into formulas and proof lines
3. **proof.rs**: Define the Proof and ProofLine structures
4. **lower_limit_logic.rs**: Implement the base logic rules
5. **abnormality.rs**: Define and detect abnormalities
6. **strategy.rs**: Implement the adaptive strategies
7. **verifier.rs**: Main verification logic
8. **main.rs**: CLI interface and orchestration

## Verification Algorithm

1. Parse the input proof
2. For each line:
   - Check if it follows from earlier lines via valid rule application
   - For conditional rules, track the abnormality conditions
   - Apply marking conditions based on the adaptive strategy
3. After processing all lines, determine which derived formulas are marked (invalidated)
4. Return verification result with explanation

## CLI Interface Design

The verifier should accept:
- Input proof files
- Strategy selection flag
- Verbosity options for detailed explanation
- Output format options

## Testing Strategy

Create test cases for:
1. Basic propositional logic inferences
2. Proofs that rely on disjunctive syllogism
3. Proofs that rely on ex falso
4. Proofs with abnormalities that should be marked under reliability
5. Proofs with abnormalities that should be marked under minimal abnormality
6. Complex proofs with multiple potential abnormality sets

## Implementation Phases

1. **Phase 1**: Implement the formula representation and parsing
2. **Phase 2**: Implement the lower limit logic rules
3. **Phase 3**: Implement proof representation and basic verification
4. **Phase 4**: Implement abnormality tracking
5. **Phase 5**: Implement adaptive strategies
6. **Phase 6**: Add CLI interface and documentation
7. **Phase 7**: Testing and refinement

## Example Usage

```
adaptive-verifier verify --file proof.txt --strategy reliability --verbose
```

Example proof file format:
```
1. P ∨ Q                         PREM
2. ¬P                           PREM
3. Q                            1,2 DisjSyll {(P ∨ Q) ∧ ¬P ∧ ¬Q}
```

## Performance Considerations

- Efficient formula equality checking and matching
- Optimization of abnormality detection
- Caching of derived consequences
- Efficient minimal abnormality set computation

## Extension Ideas

- Interactive proof development
- Proof visualization
- Support for other adaptive logics
- Automated proof search