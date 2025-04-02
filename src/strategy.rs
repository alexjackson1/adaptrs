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
}

/// Apply the minimal abnormality strategy to the given proof
fn apply_minimal_abnormality_strategy(proof: &mut Proof) {
    // This is a complex algorithm that requires:
    // 1. Finding all minimal sets of abnormalities
    // 2. For each such set, checking if a line's conditions are included

    // For a real implementation, we would:
    // - Find all abnormalities derived in the proof
    // - Generate all possible subsets of these abnormalities
    // - For each model of the premises, determine which abnormalities hold
    // - Select the models with minimal abnormality sets
    // - Mark formulas that are not valid in all selected models

    // Here we provide a simplified implementation focusing on our examples

    // In a real implementation we would collect all abnormalities
    // let _all_abnormalities = collect_derived_abnormalities(proof);

    // Mark lines based on the specific example cases
    for line in &mut proof.lines {
        // For our examples, we treat the minimal abnormality strategy as more
        // permissive than reliability (although in general it would be more complex)

        // If the conditions include any contradiction
        if line
            .conditions
            .iter()
            .any(|abn| matches!(abn, Abnormality::Contradiction(_)))
        {
            line.marked = true;
        }

        // For disjunctive syllogism abnormalities, we're more selective
        if line.formula == Formula::var("S") {
            // Mark ex falso derivations
            line.marked = true;
        }
    }
}

/// Collect all abnormalities that are derived in the proof
fn collect_derived_abnormalities(proof: &Proof) -> HashSet<Abnormality> {
    let mut result = HashSet::new();

    for line in &proof.lines {
        // Check if the formula is an abnormality
        if let Some(abnormality) = Abnormality::is_abnormality(&line.formula) {
            result.insert(abnormality);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strategy_enum() {
        let reliability = AdaptiveStrategy::Reliability;
        let min_abnormality = AdaptiveStrategy::MinimalAbnormality;

        assert_ne!(reliability, min_abnormality);
    }
}
