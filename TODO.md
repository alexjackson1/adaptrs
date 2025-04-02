# Adaptive Logic Proof Verifier - Technical Debt Items

This document outlines the remaining technical debt issues that need to be addressed for a proper, robust implementation of the adaptive logic proof verifier. The original list has been updated to remove resolved items.

## 1. Rule Application Logic (lll.rs)

### ✅ FIXED: Hardcoded Examples and Special Cases
We've removed hardcoded line numbers and special cases by:
- Updating the complex_proof.txt example to use standard logical rules
- Implementing proper rules for contrapositive equivalence and double negation
- Adding explicit condition propagation in the proof example

### 1.1 Improve Ex Falso Rule

**Current Implementation:**
The Ex Falso rule currently doesn't allow for arbitrary conclusions to be specified. It's hardcoded to use variable "S" as the conclusion.

**Needed Changes:**
- Allow the conclusion to be specified as a parameter
- Properly validate the contradiction in the premise

## 2. Abnormality Detection (abnormality.rs)

### 2.1 Implement Proper SAT-Based Formula Equivalence

**Current Implementation:**
```rust
/// Use pattern matching to check if a formula is equivalent to a DS violation
fn check_ds_violation_sat(formula: &Formula, var_mapping: &HashMap<String, u32>) -> Option<(Formula, Formula)> {
    // For now, we'll use a pattern-matching approach instead of a SAT solver
    // Look for variables in the formula that could form a DS violation
    // ...
}

/// Check if two formulas are structurally similar (simplified approach)
fn structurally_similar(f1: &Formula, f2: &Formula) -> bool {
    // This is a very simplified approach that just checks if the formulas
    // have the same structure without checking logical equivalence
    // ...
}
```

**Issues:**
- Uses structural similarity as a proxy for logical equivalence
- Cannot handle logically equivalent but structurally different formulas
- "SAT" in the function name is misleading since it doesn't actually use a SAT solver

**Needed Changes:**
- Implement proper SAT-based checking for formula equivalence
- Use the varisat library properly to determine logical equivalence

## 3. Adaptive Strategies (strategy.rs)

### ✅ FIXED: Hardcoded Proof Detection
We've removed the special case detection and hardcoded line marking in both reliability and minimal abnormality strategies.

### 3.1 Implement Proper Abnormality Derivation

**Needed Changes:**
- Improve abnormality detection and derivation logic
- Ensure derived abnormalities are properly identified in proofs

### 3.2 Implement True Minimal Abnormality Strategy

**Needed Changes:**
- Refine the implementation to correctly identify truly minimal sets of abnormalities
- Follow the theoretical literature on adaptive logics for proper implementation

## 4. Verifier Logic (verifier.rs)

### ✅ FIXED: Hardcoded Exceptions and Special Cases
We've removed special case handling and inconsistent condition validation.

### 4.1 Improve Verbosity Control

**Needed Changes:**
- Make debug output conditional on a verbosity flag
- Provide more detailed error messages for invalid proofs

## 5. Parser (parser.rs)

### 5.1 Improve Abnormality Parser

**Current Implementation:**
```rust
// Try some common patterns for our examples
if input == "(P ∨ Q) ∧ ¬P ∧ ¬Q" {
    Ok(Abnormality::DisjunctiveSyllogismViolation(
        Formula::var("P"),
        Formula::var("Q"),
    ))
} else if input == "P ∧ ¬P" {
    Ok(Abnormality::Contradiction(Formula::var("P")))
} else {
    Err(ParserError::AbnormalityParseError(format!(
        "Invalid abnormality: {}",
        input
    )))
}
```

**Issues:**
- Hardcodes exact string patterns
- Hardcodes variable names ("P", "Q")
- Falls back to specific examples rather than proper parsing

**Needed Changes:**
- Improve abnormality parser to handle general patterns
- Remove hardcoded fallbacks

## 6. Testing

### 6.1 Add More Comprehensive Tests

**Needed Changes:**
- Add tests for the new rules (DoubleNegElim, ContrapositiveEquiv)
- Add tests for proper condition propagation
- Create tests for more complex proofs with various abnormality patterns

## Priority Order for Remaining Work

1. Implement proper SAT-based abnormality detection
2. Improve the abnormality parser to handle general patterns
3. Refine the adaptive strategies implementation
4. Add comprehensive tests for all rules and strategies
5. Improve verbosity control and error reporting

## Implementation Notes

- When implementing SAT-based abnormality detection, ensure that the formulas are properly converted to CNF
- For adaptive strategies, read the theoretical literature to ensure correct implementation
- Document the expected behavior of each rule in the adaptive logic system