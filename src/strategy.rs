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

    // Find all minimal choice sets of abnormalities
    let minimal_choice_sets = find_minimal_abnormality_sets(proof, &derived_abnormalities);

    // We need to collect information about lines before modifying them to avoid borrow issues
    let line_data: Vec<(usize, Formula, HashSet<Abnormality>)> = proof
        .lines
        .iter()
        .map(|line| {
            (
                line.line_number,
                line.formula.clone(),
                line.conditions.clone(),
            )
        })
        .collect();

    // Now apply marking for each line
    for line_idx in 0..proof.lines.len() {
        let line = &mut proof.lines[line_idx];

        // A line with the empty condition set is never marked
        if line.conditions.is_empty() {
            line.marked = false;
            continue;
        }

        let line_conditions = &line_data[line_idx].2;
        let formula = &line_data[line_idx].1;

        // Apply the two conditions for marking under minimal abnormality:

        // Condition (i): Check if for all φ ∈ Φₛ(Γ), φ ∩ Δ ≠ ∅
        // In other words, is there no choice set that doesn't conflict with the line's conditions?
        let condition_i_satisfied = minimal_choice_sets.iter().all(|choice_set| {
            line_conditions
                .iter()
                .any(|condition| choice_set.contains(condition))
        });

        // If condition (i) is satisfied, mark the line
        if condition_i_satisfied {
            line.marked = true;
            continue;
        }

        // Condition (ii): For some φ ∈ Φₛ(Γ), there's no line that derives the same formula
        // with a condition set Θ such that Θ ∩ φ = ∅
        let condition_ii_satisfied = minimal_choice_sets.iter().any(|choice_set| {
            // Does this choice set not conflict with the line's conditions?
            if !line_conditions
                .iter()
                .any(|condition| choice_set.contains(condition))
            {
                // Is there no other line that derives the same formula with a condition
                // set that doesn't conflict with this choice set?
                !line_data
                    .iter()
                    .any(|(_, other_formula, other_conditions)| {
                        // Check other lines with the same formula
                        *other_formula == *formula &&
                    // The other line must have a condition set that doesn't conflict with this choice set
                    !other_conditions.iter().any(|condition| choice_set.contains(condition))
                    })
            } else {
                false
            }
        });

        // Mark the line if condition (ii) is satisfied
        line.marked = condition_ii_satisfied;
    }
}

/// Find all minimal sets of abnormalities
fn find_minimal_abnormality_sets(
    proof: &Proof,
    derived_abnormalities: &HashSet<Abnormality>,
) -> Vec<HashSet<Abnormality>> {
    // Collect the minimal Dab-formulas from the proof
    // Each Dab-formula is a disjunction of abnormalities
    // We represent it as a set of abnormalities
    let minimal_dab_formulas = collect_minimal_dab_formulas(proof, derived_abnormalities);

    // If there are no Dab-formulas, return a single empty set
    if minimal_dab_formulas.is_empty() {
        return vec![HashSet::new()];
    }

    // Compute all minimal choice sets
    compute_minimal_choice_sets(&minimal_dab_formulas)
}

/// Collect all minimal Dab-formulas from the proof
/// A Dab-formula is a disjunction of abnormalities
/// Each formula is represented as a set of abnormalities
fn collect_minimal_dab_formulas(
    proof: &Proof,
    derived_abnormalities: &HashSet<Abnormality>,
) -> Vec<HashSet<Abnormality>> {
    // In our implementation, we represent each derived abnormality as a singleton set
    // and collect them as Dab-formulas
    let mut dab_formulas: Vec<HashSet<Abnormality>> = Vec::new();

    // If there are no derived abnormalities, return empty vector
    if derived_abnormalities.is_empty() {
        return dab_formulas;
    }

    // Process derived DS violations: we treat them as separate Dab-formulas
    for abnormality in derived_abnormalities {
        if let Abnormality::DisjunctiveSyllogismViolation(_, _) = abnormality {
            let mut set = HashSet::new();
            set.insert(abnormality.clone());
            dab_formulas.push(set);
        }
    }

    // Process derived contradictions
    for abnormality in derived_abnormalities {
        if let Abnormality::Contradiction(_) = abnormality {
            let mut set = HashSet::new();
            set.insert(abnormality.clone());
            dab_formulas.push(set);
        }
    }

    // Also collect conjunctions of abnormalities from the proof's conditions
    // We need to filter for validity and only take those that are derived
    let all_conditions: Vec<HashSet<Abnormality>> = proof
        .lines
        .iter()
        .map(|line| line.conditions.clone())
        .filter(|set| !set.is_empty())
        .collect();

    for condition_set in all_conditions {
        if condition_set
            .iter()
            .any(|abn| derived_abnormalities.contains(abn))
        {
            // Only include condition sets that contain at least one derived abnormality
            let derived_subset: HashSet<Abnormality> = condition_set
                .iter()
                .filter(|abn| derived_abnormalities.contains(abn))
                .cloned()
                .collect();

            if !derived_subset.is_empty() && !dab_formulas.contains(&derived_subset) {
                dab_formulas.push(derived_subset);
            }
        }
    }

    // Remove non-minimal Dab-formulas
    filter_minimal_sets(dab_formulas)
}

/// Compute all minimal choice sets for a collection of Dab-formulas
fn compute_minimal_choice_sets(dab_formulas: &[HashSet<Abnormality>]) -> Vec<HashSet<Abnormality>> {
    // If there are no Dab-formulas, return a single empty set
    if dab_formulas.is_empty() {
        return vec![HashSet::new()];
    }

    // Initialize with the first Dab-formula
    // Create a choice set for each abnormality in the first Dab-formula
    let mut choice_sets: Vec<HashSet<Abnormality>> = dab_formulas[0]
        .iter()
        .map(|abn| {
            let mut set = HashSet::new();
            set.insert(abn.clone());
            set
        })
        .collect();

    // For each remaining Dab-formula, extend the choice sets
    for dab_formula in &dab_formulas[1..] {
        let mut new_choice_sets = Vec::new();

        // For each existing choice set and each abnormality in the current Dab-formula
        for choice_set in &choice_sets {
            for abnormality in dab_formula {
                // Create a new choice set by adding the abnormality
                let mut new_set = choice_set.clone();
                new_set.insert(abnormality.clone());
                new_choice_sets.push(new_set);
            }
        }

        // Replace old choice sets with new ones
        choice_sets = new_choice_sets;
    }

    // Filter out non-minimal choice sets
    filter_minimal_sets(choice_sets)
}

/// Filter a collection of sets to keep only the minimal ones
fn filter_minimal_sets<T: Clone + Eq + std::hash::Hash>(sets: Vec<HashSet<T>>) -> Vec<HashSet<T>> {
    let mut result: Vec<HashSet<T>> = Vec::new();

    'outer: for set in sets {
        // Check if this set is non-minimal (has a proper subset already in result)
        for existing_set in &result {
            if existing_set.is_subset(&set) && existing_set != &set {
                continue 'outer; // Skip this set as a subset exists
            }
        }

        // Remove any existing sets that are proper supersets of this set
        result.retain(|existing_set| !set.is_subset(existing_set) || set == *existing_set);

        // Add this set to the result
        result.push(set);
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

        // Create a DS violation
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

        // Check that derived abnormalities are stored in the proof
        assert_eq!(proof.derived_abnormalities.len(), 2);
    }

    #[test]
    fn test_compute_minimal_choice_sets() {
        // Create some sample Dab-formulas
        let p = Formula::var("P");
        let q = Formula::var("Q");
        let r = Formula::var("R");

        let a1 = Abnormality::contradiction(p.clone());
        let a2 = Abnormality::contradiction(q.clone());
        let a3 = Abnormality::disj_syll_violation(p.clone(), q.clone());
        // We don't use a4 in this test
        let _a4 = Abnormality::disj_syll_violation(q.clone(), r.clone());

        // Create test Dab-formulas
        let mut dab1 = HashSet::new();
        dab1.insert(a1.clone());
        dab1.insert(a2.clone());

        let mut dab2 = HashSet::new();
        dab2.insert(a2.clone());
        dab2.insert(a3.clone());

        let dab_formulas = vec![dab1, dab2];

        // Compute minimal choice sets
        let choice_sets = compute_minimal_choice_sets(&dab_formulas);

        // Expected results: {{a1, a3}, {a2}}
        // We need to select a2 from the second Dab-formula
        // Then for the first Dab-formula, we need either a1 or a2
        // If we select a2 for both, we get {a2}
        // If we select a1 for the first and a2 for the second, we get {a1, a2}
        // But {a1, a2} is not minimal because it contains {a2}
        // If we select a1 for the first and a3 for the second, we get {a1, a3}
        // So the minimal sets are {a2} and {a1, a3}

        assert_eq!(choice_sets.len(), 2);

        // Check the sets
        let expected1 = {
            let mut set = HashSet::new();
            set.insert(a2.clone());
            set
        };

        let expected2 = {
            let mut set = HashSet::new();
            set.insert(a1.clone());
            set.insert(a3.clone());
            set
        };

        assert!(choice_sets.contains(&expected1));
        assert!(choice_sets.contains(&expected2));
    }

    #[test]
    fn test_minimal_abnormality_marking() {
        // Create a proof with Minimal Abnormality strategy
        let mut proof = Proof::new(AdaptiveStrategy::MinimalAbnormality);

        // Create formulas
        let p = Formula::var("P");
        let q = Formula::var("Q");
        let p_or_q = Formula::disj(p.clone(), q.clone());
        let not_p = Formula::neg(p.clone());
        let not_q = Formula::neg(q.clone());

        // Similar to marked_proof.txt
        // 1. P ∨ Q          PREM
        // 2. ¬P             PREM
        // 3. ¬Q             PREM
        // 4. Q              1,2 DisjSyll {(P ∨ Q) ∧ ¬P ∧ ¬Q}

        let line1 = proof.add_premise(p_or_q.clone());
        let line2 = proof.add_premise(not_p.clone());
        let _line3 = proof.add_premise(not_q.clone());

        // Create DS violation condition
        let mut conditions = HashSet::new();
        let ds_violation = Abnormality::disj_syll_violation(p.clone(), q.clone()).clone();
        conditions.insert(ds_violation.clone());

        // Add Q derived conditionally via DisjSyll
        let line4 = proof.add_line(q.clone(), Rule::DisjSyll, vec![line1, line2], conditions);

        // Initially not marked
        assert!(!proof.lines[line4 - 1].marked);

        // Apply minimal abnormality strategy
        apply_minimal_abnormality_strategy(&mut proof);

        // Line 4 should be marked because the DS violation is derived
        // Line 4 uses the condition (P ∨ Q) ∧ ¬P ∧ ¬Q
        // But lines 1, 2, and 3 together derive this abnormality
        assert!(proof.lines[line4 - 1].marked);

        // Check that the derived abnormalities are stored and include our violation
        assert!(!proof.derived_abnormalities.is_empty());
        assert!(proof.derived_abnormalities.contains(&ds_violation));
    }
}
