# Adaptive Logic Implementation Guide

This document provides comprehensive guidance for implementing an adaptive logic proof verifier. It focuses specifically on the theoretical underpinnings and algorithmic approaches needed to correctly implement the key components of adaptive logic systems.

## 1. Foundational Concepts in Adaptive Logic

### 1.1 Adaptive Logic Triple

Every adaptive logic is defined by a triple `<LLL, Ω, Strategy>` where:

- **LLL** (Lower Limit Logic): The stable, monotonic core logic that determines which inferences are unconditionally valid
- **Ω** (Set of Abnormalities): A set of formulas considered abnormal; reasoning proceeds by assuming these are false unless proven otherwise
- **Strategy**: Determines how to deal with multiple minimal ways to interpret a premise set (typically Reliability or Minimal Abnormality)

### 1.2 Lower Limit Logic vs. Upper Limit Logic

**Lower Limit Logic (LLL)**:
- The monotonic base logic of the adaptive system
- All LLL-valid inferences remain valid in the adaptive logic
- Example: CLuN (paraconsistent logic) can be used as an LLL

**Upper Limit Logic (ULL)**:
- Obtained by adding to LLL all negations of abnormalities as axioms
- For many adaptive logics, this is classical logic
- Represents the "ideal" case where no abnormalities occur
- Formally: Γ ⊢ᵤₗₗ A iff Γ ∪ {¬B | B ∈ Ω} ⊢ₗₗₗ A

**Relationship**: An adaptive logic AL steers a middle course between its LLL and ULL: LLL ⊆ AL ⊆ ULL

### 1.3 CLuN as a Lower Limit Logic

CLuN is a paraconsistent logic that:
1. Retains the full positive fragment of classical logic
2. Maintains the law of excluded middle (A ∨ ¬A)
3. Treats negation in a way that avoids explosion when contradictions arise

In a CLuN-based adaptive logic, the set of abnormalities typically includes formulas of the form A ∧ ¬A (contradictions).

## 2. Proof Theory of Adaptive Logics

### 2.1 Dynamic Proof Theory

Adaptive logic proofs are dynamic, meaning the status of inferences can change as the proof progresses. The basic components include:

- **Line Format**: Each line in a proof consists of: [line number, formula, justification, condition]
- **Condition**: A set of abnormalities that are assumed to be false for that inference to be valid
- **Marking**: A mechanism to indicate when lines are "out" (not considered derived) due to derived abnormalities

### 2.2 Generic Rules

All adaptive logics have three generic rules:

1. **PREM**: Premise introduction rule
   ```
   If A ∈ Γ:
      A    ∅
   ```

2. **RU (Unconditional Rule)**: Applies any LLL inference rule
   ```
   If A₁, ..., Aₙ ⊢ₗₗₗ B:
      A₁    Δ₁
      ...   ...
      Aₙ    Δₙ
      B     Δ₁ ∪ ... ∪ Δₙ
   ```

3. **RC (Conditional Rule)**: Makes inferences that rely on abnormalities being false
   ```
   If A₁, ..., Aₙ ⊢ₗₗₗ B ∨ Dab(Θ):
      A₁    Δ₁
      ...   ...
      Aₙ    Δₙ
      B     Δ₁ ∪ ... ∪ Δₙ ∪ Θ
   ```

### 2.3 Dab-formulas

A Dab-formula is a disjunction of abnormalities: Dab(Δ) = ⋁{A | A ∈ Δ} where Δ ⊆ Ω

- A Dab-formula is **minimal** at a stage s if no proper subset of its disjuncts forms a Dab-formula at stage s
- Minimal Dab-formulas represent the minimal sets of abnormalities that must contain at least one true abnormality

## 3. Adaptive Strategies in Detail

### 3.1 Reliability Strategy

For the Reliability strategy, an abnormality is considered "unreliable" if it appears in a minimal Dab-formula. Formally:

1. Let Dab(Δ₁), Dab(Δ₂), ..., be the minimal Dab-formulas derived at stage s
2. Define Σₛ(Γ) = {Δ₁, Δ₂, ...}
3. The set of unreliable formulas Uₛ(Γ) = ⋃Σₛ(Γ)

**Marking Definition for Reliability**:
- A line with condition Δ is marked at stage s iff Δ ∩ Uₛ(Γ) ≠ ∅

**Algorithm**:
1. Identify all minimal Dab-formulas at the current stage
2. Collect all abnormalities appearing in these formulas into the set U
3. Mark any line whose condition contains at least one element from U

### 3.2 Minimal Abnormality Strategy

The Minimal Abnormality strategy is more selective about which lines to mark:

1. Let Dab(Δ₁), Dab(Δ₂), ..., be the minimal Dab-formulas derived at stage s
2. Define Σₛ(Γ) = {Δ₁, Δ₂, ...}
3. Let Φₛ(Γ) be the set of minimal choice sets of Σₛ(Γ)

A choice set φ of Σₛ(Γ) selects at least one abnormality from each minimal Dab-formula.

**Marking Definition for Minimal Abnormality**:
A line l with formula A is marked at stage s iff:
- (i) There is no φ ∈ Φₛ(Γ) such that φ ∩ Δ = ∅, or
- (ii) For some φ ∈ Φₛ(Γ), there is no line on which A is derived on a condition Θ for which Θ ∩ φ = ∅

**Algorithm**:
1. Identify all minimal Dab-formulas at the current stage
2. Compute all minimal choice sets of these Dab-formulas
3. Mark a line if either:
   - Its condition shares elements with every minimal choice set, or
   - There is a minimal choice set such that A isn't derived elsewhere on a condition disjoint from this set

### 3.3 Implementing the Minimal Abnormality Strategy

The key challenge here is efficiently finding all minimal choice sets. A SAT-based approach:

1. **Encode the problem as a SAT instance**:
   - For each abnormality a, create a variable x_a
   - For each minimal Dab-formula Dab(Δᵢ), create a clause ⋁{x_a | a ∈ Δᵢ}
   - The goal is to find all minimal models satisfying these clauses

2. **Find all minimal models**:
   - Start with any satisfying model M
   - Record M as a minimal model
   - Add a blocking clause excluding M and all its supersets
   - Repeat until unsatisfiable
   - For each minimal model found, convert back to the corresponding choice set

3. **Optimization techniques**:
   - Use incremental SAT solving
   - Prioritize abnormalities that appear in fewer Dab-formulas
   - Exploit structural properties of the Dab-formulas

## 4. Determining When Abnormalities are Derived

### 4.1 Derivation of Abnormalities

An abnormality is considered "derived" at stage s if:

1. It appears as a line in the proof on the empty condition, or
2. It is a disjunct in a Dab-formula derived on the empty condition

Importantly, a Dab-formula is only considered derived if it's derived on the empty condition, meaning it's an unconditional consequence of the premises.

### 4.2 Minimality of Dab-formulas

A Dab-formula Dab(Δ) is minimal at stage s if there is no other Dab-formula Dab(Δ') at stage s such that Δ' ⊂ Δ.

**Algorithm for maintaining minimal Dab-formulas**:
1. When a new Dab-formula Dab(Δ) is derived:
   - Check if there's any already recorded minimal Dab-formula Dab(Δ') where Δ' ⊂ Δ
   - If yes, discard Dab(Δ) as non-minimal
   - If no, add Dab(Δ) to the list of minimal Dab-formulas
   - Remove any existing Dab-formula Dab(Δ") where Δ ⊂ Δ"

## 5. Formula Equivalence in Adaptive Logic

### 5.1 Defining Equivalence

In adaptive logic, formula equivalence should be defined according to the underlying LLL:

- Two formulas A and B are equivalent iff A ⊢ₗₗₗ B and B ⊢ₗₗₗ A
- For conditions (sets of abnormalities), set equivalence should be used

### 5.2 Handling Equivalence in Implementation

When implementing an adaptive logic proof verifier:

1. Use a canonical representation for formulas according to LLL
2. For CLuN, be careful with negation handling as formulas like ¬¬A are not equivalent to A
3. When checking if an abnormality appears in a condition, use proper equivalence checking based on LLL
4. For most practical purposes, syntactic identity can be used for abnormalities, but semantic equivalence may be necessary in complex cases

## 6. Final Derivability and Semantics

### 6.1 Final Derivability

A formula is considered "finally derived" if it appears on a line that won't be marked in any extension of the proof:

A is finally derived from Γ at line l of stage s iff:
1. A is the formula of line l
2. Line l is unmarked at s
3. Any extension of s in which line l is marked can be further extended to a stage where line l is unmarked again

### 6.2 Semantics of Adaptive Logics

The semantics of adaptive logics is defined in terms of selecting "preferred" models:

1. For Reliability:
   - Define U(Γ) as the set of all abnormalities that appear in minimal Dab-consequences of Γ
   - A LLL-model M of Γ is reliable iff Ab(M) ⊆ U(Γ)
   - Γ ⊨ₐₗᵣ A iff A is verified by all reliable models of Γ

2. For Minimal Abnormality:
   - A LLL-model M of Γ is minimally abnormal iff there is no LLL-model M' of Γ such that Ab(M') ⊂ Ab(M)
   - Γ ⊨ₐₗₘ A iff A is verified by all minimally abnormal models of Γ

## 7. Implementation Guidelines

### 7.1 Core Components

An adaptive logic proof verifier should include:

1. **Formula Parser**: Parse and represent logical formulas
2. **LLL Reasoner**: Implement or interface with an LLL theorem prover
3. **Proof State Manager**: Track lines, justifications, conditions, and markings
4. **Abnormality Tracker**: Maintain minimal Dab-formulas and compute unreliable abnormalities
5. **Marking Engine**: Implement marking criteria for the chosen strategy

### 7.2 Algorithm for Proof Verification

```pseudocode
function VerifyProof(proof, premises, triple):
    lll, abnormalities, strategy = triple
    lines = []
    minimal_dabs = []
    
    for line in proof:
        number, formula, justification, condition = line
        
        if justification is PREM:
            if formula in premises:
                lines.append(Line(number, formula, justification, []))
            else:
                return "Invalid premise"
                
        elif justification is RU:
            ref_lines = GetReferencedLines(justification, lines)
            ref_formulas = [line.formula for line in ref_lines]
            if lll.proves(ref_formulas, formula):
                new_condition = UnionConditions(ref_lines)
                lines.append(Line(number, formula, justification, new_condition))
            else:
                return "Invalid RU application"
                
        elif justification is RC:
            ref_lines = GetReferencedLines(justification, lines)
            ref_formulas = [line.formula for line in ref_lines]
            for abnormality_set in PossibleConditions(formula, ref_formulas, abnormalities):
                if lll.proves(ref_formulas, formula + "or" + Dab(abnormality_set)):
                    new_condition = UnionConditions(ref_lines) + abnormality_set
                    lines.append(Line(number, formula, justification, new_condition))
                    break
            else:
                return "Invalid RC application"
        
        # Update minimal Dab-formulas
        if IsDabFormula(formula) and not line.condition:
            UpdateMinimalDabs(minimal_dabs, ExtractAbnormalities(formula))
        
        # Apply marking
        if strategy == "Reliability":
            ApplyReliabilityMarking(lines, minimal_dabs)
        elif strategy == "MinimalAbnormality":
            ApplyMinimalAbnormalityMarking(lines, minimal_dabs)
    
    return "Valid proof"
```

### 7.3 Special Considerations for CLuN

When implementing an adaptive logic with CLuN as the LLL:

1. Properly handle paraconsistent negation (¬)
2. Implement correct equivalence checking respecting CLuN's treatment of negation
3. For abnormalities of the form A ∧ ¬A, ensure proper handling of subformulas and complex expressions

## 8. Handling Complex Examples

### 8.1 Dealing with Prioritized Adaptive Logics

For lexicographic or prioritized adaptive logics:

1. Maintain separate sets of abnormalities for each priority level
2. Mark lines by first considering highest priority abnormalities, then proceeding to lower priorities
3. Use a lexicographic ordering for comparing sets of abnormalities

### 8.2 Handling Other Strategies

For more exotic strategies like Normal Selections:

- Implement customized marking definitions
- Adjust the abnormality tracking mechanisms accordingly
- Ensure that the theoretical properties of the strategy are preserved

## 9. Testing and Validation

### 9.1 Test Cases

Develop test cases covering:

1. Basic adaptive logic principles
2. Known challenging examples from the literature
3. Edge cases for marking under different strategies
4. Complex interactions between abnormalities

### 9.2 Validation Criteria

Verify the implementation by checking:

1. Soundness: All derived formulas should be semantically valid
2. Completeness: All valid formulas should be derivable
3. Marking correctness: Lines should be marked according to the theoretical definitions
4. Strategy compliance: The implementation should faithfully capture the chosen strategy

## 10. Common Pitfalls and Solutions

1. **Incorrectly identifying minimal Dab-formulas**
   - Solution: Implement proper subset checking and maintain a normalized representation

2. **Inefficient handling of minimal choice sets**
   - Solution: Use specialized algorithms for minimal hitting set computation

3. **Incorrect marking for Minimal Abnormality**
   - Solution: Carefully implement both conditions of the marking definition

4. **Overlooking equivalence of formulas**
   - Solution: Implement proper semantic equivalence checking based on LLL

5. **Failing to handle complex abnormalities**
   - Solution: Use a general representation that can handle arbitrary formulas as abnormalities

## Appendix: Examples and Algorithms

### A.1 Example: Computing Minimal Choice Sets

```python
def compute_minimal_choice_sets(dab_formulas):
    """
    Compute all minimal choice sets for a collection of Dab-formulas.
    
    Args:
        dab_formulas: List of sets, where each set contains abnormalities
                      from a minimal Dab-formula
    
    Returns:
        List of minimal choice sets
    """
    if not dab_formulas:
        return [set()]
    
    result = []
    remaining = dab_formulas[1:]
    
    # For each abnormality in the first Dab-formula
    for abnormality in dab_formulas[0]:
        # Recursively compute choice sets for remaining Dab-formulas
        for choice_set in compute_minimal_choice_sets(remaining):
            new_set = choice_set.union({abnormality})
            
            # Check if this set is minimal
            if all(not new_set.issuperset(s) for s in result):
                # Remove any existing sets that are supersets of this one
                result = [s for s in result if not s.issuperset(new_set)]
                result.append(new_set)
    
    return result
```

### A.2 Example: Reliability Marking

```python
def apply_reliability_marking(lines, minimal_dabs):
    """
    Apply marking according to the Reliability strategy.
    
    Args:
        lines: List of Line objects in the proof
        minimal_dabs: List of minimal Dab-formulas (as sets of abnormalities)
    """
    # Compute unreliable abnormalities
    unreliable = set().union(*minimal_dabs)
    
    # Mark lines whose condition contains unreliable abnormalities
    for line in lines:
        if any(abnormality in unreliable for abnormality in line.condition):
            line.marked = True
        else:
            line.marked = False
```

### A.3 Example: Minimal Abnormality Marking

```python
def apply_minimal_abnormality_marking(lines, minimal_dabs):
    """
    Apply marking according to the Minimal Abnormality strategy.
    
    Args:
        lines: List of Line objects in the proof
        minimal_dabs: List of minimal Dab-formulas (as sets of abnormalities)
    """
    # Compute minimal choice sets
    choice_sets = compute_minimal_choice_sets(minimal_dabs)
    
    # Apply marking criteria
    for line in lines:
        # Condition (i): Check if line's condition shares elements with all choice sets
        if all(any(abnormality in choice_set for abnormality in line.condition) 
               for choice_set in choice_sets):
            line.marked = True
            continue
        
        # Condition (ii): Check if there's a choice set with no compatible derivation
        for choice_set in choice_sets:
            # Check if any line derives the same formula with a compatible condition
            compatible_derivation = False
            for other_line in lines:
                if (other_line.formula == line.formula and 
                    not any(abnormality in choice_set for abnormality in other_line.condition)):
                    compatible_derivation = True
                    break
            
            if not compatible_derivation:
                line.marked = True
                break
        else:
            line.marked = False
```
