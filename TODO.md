# Adaptive Logic Proof Verifier - Technical Debt Items

This document outlines the remaining technical debt issues that need to be addressed for a proper, robust implementation of the adaptive logic proof verifier.

## Completed Tasks and Fixes

### ✅ Rule Application Logic (lll.rs)
- **Removed hardcoded examples and special cases**: Updated to use standard logical rules, implemented proper rules for contrapositive equivalence and double negation, added explicit condition propagation
- **Improved Ex Falso rule**: Added parameter-based conclusion specification, proper contradiction validation, removed hardcoded variable "S"

### ✅ Abnormality Detection (abnormality.rs)
- **Implemented proper SAT-based formula equivalence**: Added CNF conversion, SAT-based logical equivalence, replaced structural similarity with proper equivalence
- **Fixed string-based comparisons**: Replaced string manipulation with direct Formula object comparison

### ✅ Adaptive Strategies (strategy.rs)
- **Removed hardcoded proof detection**: Eliminated special case detection and hardcoded line marking
- **Removed debug print statements**: Replaced with proper state storage in the proof structure

### ✅ Parser (parser.rs)
- **Improved abnormality parser**: Added support for complex patterns, removed hardcoded strings, added general pattern detection, added Unicode/ASCII support

### ✅ Verifier Logic (verifier.rs)
- **Removed hardcoded exceptions**: Eliminated special case handling, fixed inconsistent validation

### ✅ Testing
- **Fixed failing tests**: Updated for new CNF conversion, logical equivalence, improved abnormality detection, and edge cases

### ✅ User Interface
- **Improved proof display**: Changed marking symbol from ✓ to ✗ to clearly indicate invalid lines
- **Enhanced abnormality reporting**: Added structured abnormality display in CLI

## Priority Items for Future Work

### 1. Abnormality Derivation (strategy.rs)
**Current Issues:**
- The implementation doesn't correctly identify all abnormalities in complex formulas
- There may be inconsistencies between abnormality detection and strategy application

**Needed Changes:**
- Fix abnormality detection for complex formulas
- Ensure proper identification of derived abnormalities
- Add unit tests for comprehensive coverage

### 2. Minimal Abnormality Strategy (strategy.rs)
**Current Issues:**
- Simplified heuristic at lines 104-120 is not theoretically sound
- Comment at line 86: "In a full implementation, this would use the SAT solver to find all minimal models"

**Needed Changes:**
- Implement SAT-based minimal model finder
- Follow theoretical literature for proper implementation
- Improve test_minimal_abnormality_sets for verification
- Add comprehensive test cases with expected outcomes

### 3. Error Handling
**Current Issues:**
- Functions return `Option<T>` without context
- No standardized approach across codebase
- Insufficient detail in error messages

**Needed Changes:**
- Create appropriate error enums for each module
- Replace `Option<T>` with `Result<T, Error>` with context
- Standardize error propagation
- Add detailed messages for all error cases

### 4. Testing Improvements
**Needed Changes:**
- Add tests for new rules (DoubleNegElim, ContrapositiveEquiv)
- Create tests for complex proofs with various abnormality patterns
- Add property-based testing for formula equivalence
- Test all edge cases in abnormality parser

## Architectural Issues to Address

### 1. Separation of Concerns
- Verification and marking are tightly coupled in verifier.rs
- Parser has direct dependency on abnormality logic rather than just building ASTs

### 2. Algorithmic Efficiency
- Abnormality detection is inefficient and could benefit from caching
- Minimal abnormality algorithm needs optimization for complex cases

### 3. Command-Line Interface
- Add support for multiple file processing
- Implement configuration file support
- Expand strategy options with additional parameters

## Implementation Notes

- Read theoretical literature on adaptive logics for correct implementation of minimal abnormality
- Document expected behavior of each logical rule
- Consider caching mechanism for expensive computations
- Standardize error handling across the codebase
- Use property-based testing for logical equivalence
- Consider implementing a more systematic approach for temporary variable naming in Tseitin transformation