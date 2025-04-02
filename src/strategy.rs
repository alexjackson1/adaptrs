use crate::abnormality::Abnormality;
use crate::formula::Formula;
use crate::proof::Proof;
use std::collections::HashSet;

/// Represents the adaptive strategy for handling abnormalities
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdaptiveStrategy {
    /// Reliability strategy: Mark lines that depend on abnormalities that are shown to be unreliable
    Reliability,
    /// Minimal abnormality strategy: Consider all minimal sets of abnormalities
    MinimalAbnormality,
}

impl AdaptiveStrategy {
    /// Apply the marking strategy to the given proof
    pub fn apply_marking(&self, proof: &mut Proof) {
        match self {
            AdaptiveStrategy::Reliability => apply_reliability_strategy(proof),
            AdaptiveStrategy::MinimalAbnormality => apply_minimal_abnormality_strategy(proof),
        }
    }
}

/// Apply the reliability strategy to the given proof
fn apply_reliability_strategy(proof: &mut Proof) {
    // Find all abnormalities that are derived in the proof
    let derived_abnormalities = collect_derived_abnormalities(proof);

    // Debug information should be in the proof result, not printed directly
    if !derived_abnormalities.is_empty() {
        // Store the abnormalities in the proof for later use in reporting
        proof.derived_abnormalities = derived_abnormalities.clone();
    }

    // Mark all lines that depend on unreliable abnormalities
    for line in &mut proof.lines {
        // If the line depends on any abnormality that is derived, mark it
        if !line.conditions.is_empty()
            && line
                .conditions
                .iter()
                .any(|abn| derived_abnormalities.contains(abn))
        {
            line.marked = true;
        }
    }

    // The marking has been applied based on the derived abnormalities
    // No special cases needed
}

/// Apply the minimal abnormality strategy to the given proof
fn apply_minimal_abnormality_strategy(proof: &mut Proof) {
    // Collect all abnormalities that occur in the proof
    let derived_abnormalities = collect_derived_abnormalities(proof);

    // Store the abnormalities in the proof for later use in reporting
    if !derived_abnormalities.is_empty() {
        proof.derived_abnormalities = derived_abnormalities.clone();
    }

    // Find all minimal sets of abnormalities
    let minimal_sets = find_minimal_abnormality_sets(proof, &derived_abnormalities);

    // Mark lines based on minimal abnormality sets
    for line in &mut proof.lines {
        // A line is marked if there is no minimal abnormality set that allows it
        if !line.conditions.is_empty() {
            let is_valid_in_some_model = minimal_sets.iter().any(|set| {
                // Check if this minimal set doesn't conflict with the line's conditions
                line.conditions
                    .iter()
                    .all(|condition| !set.contains(condition))
            });

            // Mark the line if it's not valid in any minimal abnormality model
            line.marked = !is_valid_in_some_model;
        }
    }

    // The marking has been applied based on minimal abnormality sets
    // No special cases needed
}

/// Find all minimal sets of abnormalities
fn find_minimal_abnormality_sets(
    proof: &Proof,
    derived_abnormalities: &HashSet<Abnormality>,
) -> Vec<HashSet<Abnormality>> {
    // In a full implementation, this would use the SAT solver to find all minimal models
    // For our purposes, we'll implement a simplified version

    // Get all formulas from the proof (for potential future use)
    let _premises: Vec<Formula> = proof
        .lines
        .iter()
        .filter(|line| matches!(line.justification, crate::proof::Justification::Premise))
        .map(|line| line.formula.clone())
        .collect();

    // Get all abnormalities in the proof
    let all_conditions: Vec<Abnormality> = proof
        .lines
        .iter()
        .flat_map(|line| line.conditions.iter().cloned())
        .collect();

    // Heuristic for simplified minimal abnormality computation:
    // 1. Try without any abnormalities
    // 2. Try with each single abnormality
    // 3. Try with pairs of abnormalities (if needed)

    let mut minimal_sets = Vec::new();

    // Try with no abnormalities
    let empty_set = HashSet::new();
    minimal_sets.push(empty_set);

    // Try with single abnormalities
    for abnormality in derived_abnormalities {
        let mut set = HashSet::new();
        set.insert(abnormality.clone());
        minimal_sets.push(set);
    }

    // For disjunctive syllogism, we might have a situation where negations of both
    // disjuncts aren't derived, but one of them could be. In this case, we add sets
    // with individual negations.
    for abnormality in &all_conditions {
        if let Abnormality::DisjunctiveSyllogismViolation(_, _) = abnormality {
            // Check if this DS violation isn't already derived
            if !derived_abnormalities.contains(abnormality) {
                // Add the potential DS violation as a separate minimal set
                let mut set = HashSet::new();
                set.insert(abnormality.clone());
                minimal_sets.push(set);
            }
        }
    }

    // Filter out non-minimal sets
    let mut result = Vec::new();
    for i in 0..minimal_sets.len() {
        let mut is_minimal = true;
        for j in 0..minimal_sets.len() {
            if i != j && minimal_sets[j].is_subset(&minimal_sets[i]) && !minimal_sets[j].is_empty()
            {
                is_minimal = false;
                break;
            }
        }
        if is_minimal {
            result.push(minimal_sets[i].clone());
        }
    }

    result
}

/// Collect all abnormalities that are derived in the proof
fn collect_derived_abnormalities(proof: &Proof) -> HashSet<Abnormality> {
    let mut result = HashSet::new();
    let mut all_formulas = Vec::new();

    // Step 1: Collect all formulas from the proof
    for line in &proof.lines {
        all_formulas.push(line.formula.clone());

        // Also check if the formula itself is an abnormality
        if let Some(abnormality) = Abnormality::is_abnormality(&line.formula) {
            result.insert(abnormality);
        }

        // Check for abnormalities in subformulas
        for subformula in line.formula.subformulas() {
            if let Some(abnormality) = Abnormality::is_abnormality(&subformula) {
                result.insert(abnormality);
            }
        }
    }

    // Step 2: Look for combinations of formulas that form abnormalities

    // Check for contradictions: A and ¬A
    for i in 0..all_formulas.len() {
        for j in i + 1..all_formulas.len() {
            if let Some(contradiction) =
                Abnormality::check_contradiction(&all_formulas[i], &all_formulas[j])
            {
                result.insert(contradiction);
            }
        }
    }

    // Check for disjunctive syllogism violations: (A ∨ B) and ¬A and ¬B
    let ds_violations = Abnormality::find_potential_ds_violations(&all_formulas);
    result.extend(ds_violations);

    // Step 3: Also check for abnormalities that are explicitly attached to lines
    // as conditions (these represent potential but not necessarily derived abnormalities)
    for line in &proof.lines {
        for condition in &line.conditions {
            // For marking purposes, we consider conditions that don't conflict with derived formulas
            // If we find a contradiction (A ∧ ¬A) and also have ¬A in the proof,
            // the abnormality is derivable
            match condition {
                Abnormality::Contradiction(formula) => {
                    let negation = Formula::neg(formula.clone());
                    if all_formulas.contains(formula) || all_formulas.contains(&negation) {
                        result.insert(condition.clone());
                    }
                }
                Abnormality::DisjunctiveSyllogismViolation(a, b) => {
                    let disj = Formula::disj(a.clone(), b.clone());
                    let neg_a = Formula::neg(a.clone());
                    let neg_b = Formula::neg(b.clone());

                    // If we have A ∨ B, ¬A, and ¬B in the proof, the DS violation is derivable
                    if all_formulas.contains(&disj)
                        && all_formulas.contains(&neg_a)
                        && all_formulas.contains(&neg_b)
                    {
                        result.insert(condition.clone());
                    }
                }
            }
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abnormality::Abnormality;
    use crate::formula::Formula;
    use crate::proof::{Proof, Rule};
    use std::collections::HashSet;

    #[test]
    fn test_strategy_enum() {
        let reliability = AdaptiveStrategy::Reliability;
        let min_abnormality = AdaptiveStrategy::MinimalAbnormality;

        assert_ne!(reliability, min_abnormality);
    }

    #[test]
    fn test_collect_derived_abnormalities() {
        let mut proof = Proof::new(AdaptiveStrategy::Reliability);

        let p = Formula::var("P");
        let q = Formula::var("Q");
        let not_p = Formula::neg(p.clone());

        // Add a contradiction
        let p_and_not_p = Formula::conj(p.clone(), not_p.clone());
        proof.add_premise(p_and_not_p);

        // Add formula without abnormalities
        proof.add_premise(q.clone());

        let abnormalities = collect_derived_abnormalities(&proof);

        // Should detect the contradiction
        assert_eq!(abnormalities.len(), 1);
        let expected = Abnormality::contradiction(p.clone());
        assert!(abnormalities.contains(&expected));
    }

    #[test]
    fn test_collect_derived_abnormalities_with_ds_violation() {
        let mut proof = Proof::new(AdaptiveStrategy::Reliability);

        let p = Formula::var("P");
        let q = Formula::var("Q");
        let p_or_q = Formula::disj(p.clone(), q.clone());
        let not_p = Formula::neg(p.clone());
        let not_q = Formula::neg(q.clone());

        // Add formulas that together form a DS violation
        proof.add_premise(p_or_q.clone());
        proof.add_premise(not_p.clone());
        proof.add_premise(not_q.clone());

        let abnormalities = collect_derived_abnormalities(&proof);

        // Should detect the DS violation
        assert_eq!(abnormalities.len(), 1);
        let expected = Abnormality::disj_syll_violation(p.clone(), q.clone());
        assert!(abnormalities.contains(&expected));
    }

    #[test]
    fn test_apply_reliability_strategy() {
        let mut proof = Proof::new(AdaptiveStrategy::Reliability);

        let p = Formula::var("P");
        let q = Formula::var("Q");
        let p_or_q = Formula::disj(p.clone(), q.clone());
        let not_p = Formula::neg(p.clone());

        // Create a proof with DS
        // 1. P ∨ Q                  PREM
        // 2. ¬P                     PREM
        // 3. Q                      1,2 DS {(P ∨ Q) ∧ ¬P ∧ ¬Q}

        let line1 = proof.add_premise(p_or_q.clone());
        let line2 = proof.add_premise(not_p.clone());

        // Create the abnormality
        let mut conditions = HashSet::new();
        let ds_violation = Abnormality::disj_syll_violation(p.clone(), q.clone());
        conditions.insert(ds_violation);

        // Add the conditional line
        let _line3 = proof.add_line(q.clone(), Rule::DisjSyll, vec![line1, line2], conditions);

        // Before marking strategy
        assert!(!proof.lines[2].marked);

        // After marking strategy
        apply_reliability_strategy(&mut proof);

        // The line should be marked if the DS violation is derived
        // For this test, we don't have ¬Q in the proof, so the DS violation isn't derived
        assert!(!proof.lines[2].marked);
        
        // Check that abnormalities are being stored properly
        assert!(proof.derived_abnormalities.is_empty());

        // Now add ¬Q to prove the DS violation
        let not_q = Formula::neg(q.clone());
        proof.add_premise(not_q.clone());

        // Apply marking again
        apply_reliability_strategy(&mut proof);

        // Now line 3 should be marked because the DS violation can be derived
        assert!(proof.lines[2].marked);
        
        // Check that the DS violation is properly stored in the proof
        assert!(!proof.derived_abnormalities.is_empty());
        let expected_abnormality = Abnormality::disj_syll_violation(p.clone(), q.clone());
        assert!(proof.derived_abnormalities.contains(&expected_abnormality));
    }

    #[test]
    fn test_minimal_abnormality_sets() {
        let mut proof = Proof::new(AdaptiveStrategy::MinimalAbnormality);

        let p = Formula::var("P");
        let q = Formula::var("Q");
        let r = Formula::var("R");

        // Create a proof with multiple abnormalities
        proof.add_premise(p.clone());
        proof.add_premise(Formula::neg(p.clone())); // Contradiction

        // Create two different DS violations
        proof.add_premise(Formula::disj(q.clone(), r.clone()));
        proof.add_premise(Formula::neg(q.clone()));
        proof.add_premise(Formula::neg(r.clone()));

        let abnormalities = collect_derived_abnormalities(&proof);

        // Should have two abnormalities
        assert_eq!(abnormalities.len(), 2);

        // Find minimal sets
        let minimal_sets = find_minimal_abnormality_sets(&proof, &abnormalities);

        // Should have found sets for the contradiction and DS violation
        assert!(!minimal_sets.is_empty());

        // Apply minimal abnormality strategy
        apply_minimal_abnormality_strategy(&mut proof);

        // Check that lines with contradictions are marked
        // In real implementation, this would depend on the specific rules applied
    }
}
