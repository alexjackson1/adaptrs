use crate::formula::Formula;
use itertools::Itertools;
use std::collections::{HashMap, HashSet};
use std::fmt;

/// Represents an abnormality in the adaptive logic system
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Abnormality {
    /// Disjunctive syllogism violation: (A ∨ B) ∧ ¬A ∧ ¬B
    DisjunctiveSyllogismViolation(Formula, Formula),
    /// Contradiction: A ∧ ¬A
    Contradiction(Formula),
}

impl Abnormality {
    /// Creates a new disjunctive syllogism violation abnormality
    pub fn disj_syll_violation(a: Formula, b: Formula) -> Self {
        Abnormality::DisjunctiveSyllogismViolation(a, b)
    }

    /// Creates a new contradiction abnormality
    pub fn contradiction(formula: Formula) -> Self {
        Abnormality::Contradiction(formula)
    }

    /// Returns the formula representing this abnormality
    pub fn to_formula(&self) -> Formula {
        match self {
            Abnormality::DisjunctiveSyllogismViolation(a, b) => {
                let disj = Formula::disj(a.clone(), b.clone());
                let neg_a = Formula::neg(a.clone());
                let neg_b = Formula::neg(b.clone());
                Formula::conj(disj, Formula::conj(neg_a, neg_b))
            }
            Abnormality::Contradiction(a) => Formula::conj(a.clone(), Formula::neg(a.clone())),
        }
    }

    /// Checks if the given formula is an abnormality
    pub fn is_abnormality(formula: &Formula) -> Option<Abnormality> {
        // Check for contradictions: A ∧ ¬A or ¬A ∧ A
        if let Formula::Conj(left, right) = formula {
            if let Formula::Neg(inner) = &**left {
                if **inner == **right {
                    return Some(Abnormality::Contradiction((**right).clone()));
                }
            } else if let Formula::Neg(inner) = &**right {
                if **inner == **left {
                    return Some(Abnormality::Contradiction((**left).clone()));
                }
            }
        }

        // Check for disjunctive syllogism violations: (A ∨ B) ∧ ¬A ∧ ¬B
        if let Some((a, b)) = Self::is_disj_syll_violation(formula) {
            return Some(Abnormality::DisjunctiveSyllogismViolation(a, b));
        }

        None
    }

    /// Check if a formula represents a disjunctive syllogism violation: (A ∨ B) ∧ ¬A ∧ ¬B
    fn is_disj_syll_violation(formula: &Formula) -> Option<(Formula, Formula)> {
        // For a proper implementation, we need to check if the formula is equivalent to a DS violation
        // This involves normalizing the formula and checking its structure

        // First, check for the pattern (A ∨ B) ∧ ¬A ∧ ¬B
        if let Formula::Conj(first, rest) = formula {
            if let Formula::Disj(a, b) = &**first {
                if let Formula::Conj(second, third) = &**rest {
                    // Check for negations of A and B
                    if Self::is_negation_of(second, a) && Self::is_negation_of(third, b) {
                        return Some(((**a).clone(), (**b).clone()));
                    } else if Self::is_negation_of(second, b) && Self::is_negation_of(third, a) {
                        return Some(((**b).clone(), (**a).clone()));
                    }
                }
            }
        }

        // Check for more complex structures like ((P ∨ Q) ∧ ¬P) ∧ ¬Q
        if let Formula::Conj(left, right) = formula {
            if let Formula::Conj(inner_left, inner_right) = &**left {
                if let Formula::Disj(a, b) = &**inner_left {
                    if Self::is_negation_of(inner_right, a) && Self::is_negation_of(right, b) {
                        return Some(((**a).clone(), (**b).clone()));
                    } else if Self::is_negation_of(inner_right, b) && Self::is_negation_of(right, a)
                    {
                        return Some(((**b).clone(), (**a).clone()));
                    }
                }
            }
        }

        // Use pattern matching to check if this formula is equivalent to a DS violation
        let var_mapping = Self::collect_variables(formula);
        if let Some((a, b)) = Self::check_ds_violation_sat(formula, &var_mapping) {
            return Some((a, b));
        }

        None
    }

    /// Check if one formula is the negation of another
    fn is_negation_of(possible_neg: &Formula, formula: &Box<Formula>) -> bool {
        if let Formula::Neg(inner) = possible_neg {
            return **inner == **formula;
        }
        false
    }

    /// Collect all variables in a formula and create a mapping to indices
    fn collect_variables(formula: &Formula) -> HashMap<String, u32> {
        let mut variables = HashMap::new();
        let mut var_index = 1;

        for subformula in formula.subformulas() {
            if let Formula::Var(name) = &subformula {
                if !variables.contains_key(name) {
                    variables.insert(name.clone(), var_index);
                    var_index += 1;
                }
            }
        }

        variables
    }

    /// Use pattern matching to check if a formula is equivalent to a DS violation
    fn check_ds_violation_sat(
        formula: &Formula,
        var_mapping: &HashMap<String, u32>,
    ) -> Option<(Formula, Formula)> {
        // For now, we'll use a pattern-matching approach instead of a SAT solver
        // Look for variables in the formula that could form a DS violation

        if var_mapping.len() >= 2 {
            let variables: Vec<String> = var_mapping.keys().cloned().collect();

            // Try all pairs of variables as potential candidates for a DS violation
            for combo in variables.iter().combinations(2) {
                let a_name = combo[0];
                let b_name = combo[1];

                let a = Formula::var(a_name);
                let b = Formula::var(b_name);

                // Construct a DS violation formula
                let ds_violation = Self::construct_ds_violation(&a, &b);

                // Compare structure rather than using a SAT solver
                if Self::structurally_similar(formula, &ds_violation) {
                    return Some((a, b));
                }
            }
        }

        None
    }

    /// Construct a disjunctive syllogism violation formula
    fn construct_ds_violation(a: &Formula, b: &Formula) -> Formula {
        let disj = Formula::disj(a.clone(), b.clone());
        let neg_a = Formula::neg(a.clone());
        let neg_b = Formula::neg(b.clone());
        Formula::conj(disj, Formula::conj(neg_a, neg_b))
    }

    /// Check if two formulas are structurally similar (simplified approach)
    fn structurally_similar(f1: &Formula, f2: &Formula) -> bool {
        // This is a very simplified approach that just checks if the formulas
        // have the same structure without checking logical equivalence
        match (f1, f2) {
            (Formula::Var(_), Formula::Var(_)) => true,
            (Formula::Neg(a), Formula::Neg(b)) => Self::structurally_similar(a, b),
            (Formula::Conj(a1, a2), Formula::Conj(b1, b2)) => {
                (Self::structurally_similar(a1, b1) && Self::structurally_similar(a2, b2))
                    || (Self::structurally_similar(a1, b2) && Self::structurally_similar(a2, b1))
            }
            (Formula::Disj(a1, a2), Formula::Disj(b1, b2)) => {
                (Self::structurally_similar(a1, b1) && Self::structurally_similar(a2, b2))
                    || (Self::structurally_similar(a1, b2) && Self::structurally_similar(a2, b1))
            }
            (Formula::Impl(a1, a2), Formula::Impl(b1, b2)) => {
                Self::structurally_similar(a1, b1) && Self::structurally_similar(a2, b2)
            }
            (Formula::Bicon(a1, a2), Formula::Bicon(b1, b2)) => {
                (Self::structurally_similar(a1, b1) && Self::structurally_similar(a2, b2))
                    || (Self::structurally_similar(a1, b2) && Self::structurally_similar(a2, b1))
            }
            _ => false,
        }
    }

    /// Detect all abnormalities in a formula
    pub fn detect_abnormalities(formula: &Formula) -> HashSet<Abnormality> {
        let mut result = HashSet::new();

        // Check if the formula itself is an abnormality
        if let Some(abnormality) = Self::is_abnormality(formula) {
            result.insert(abnormality);
        }

        // Recursively check all subformulas
        for subformula in formula.subformulas() {
            if let Some(abnormality) = Self::is_abnormality(&subformula) {
                result.insert(abnormality);
            }
        }

        result
    }

    /// Check if two formulas form a contradiction
    pub fn check_contradiction(f1: &Formula, f2: &Formula) -> Option<Abnormality> {
        if let Formula::Neg(inner) = f1 {
            if **inner == *f2 {
                return Some(Abnormality::Contradiction((**inner).clone()));
            }
        } else if let Formula::Neg(inner) = f2 {
            if **inner == *f1 {
                return Some(Abnormality::Contradiction(f1.clone()));
            }
        }
        None
    }

    /// Identify potential disjunctive syllogism abnormalities from a set of formulas
    pub fn find_potential_ds_violations(formulas: &[Formula]) -> HashSet<Abnormality> {
        let mut result = HashSet::new();

        // Look for disjunctions and negations that could form a DS violation
        let disjunctions: Vec<_> = formulas
            .iter()
            .filter_map(|f| {
                if let Formula::Disj(a, b) = f {
                    Some((a, b))
                } else {
                    None
                }
            })
            .collect();

        let negations: Vec<_> = formulas
            .iter()
            .filter_map(|f| {
                if let Formula::Neg(inner) = f {
                    Some(inner)
                } else {
                    None
                }
            })
            .collect();

        // For each disjunction A ∨ B, look for negations ¬A and ¬B
        for (a, b) in disjunctions {
            // Check if negations of both disjuncts exist in the set of formulas
            let has_neg_a = negations.iter().any(|neg| ***neg == **a);
            let has_neg_b = negations.iter().any(|neg| ***neg == **b);

            if has_neg_a && has_neg_b {
                result.insert(Abnormality::disj_syll_violation(
                    (**a).clone(),
                    (**b).clone(),
                ));
            }
        }

        result
    }
}

impl fmt::Display for Abnormality {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Abnormality::DisjunctiveSyllogismViolation(a, b) => {
                write!(f, "({} ∨ {}) ∧ ¬{} ∧ ¬{}", a, b, a, b)
            }
            Abnormality::Contradiction(a) => {
                write!(f, "{} ∧ ¬{}", a, a)
            }
        }
    }
}

/// A set of abnormality conditions
pub type AbnormalitySet = HashSet<Abnormality>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abnormality_creation() {
        let p = Formula::var("P");
        let q = Formula::var("Q");

        let contradiction = Abnormality::contradiction(p.clone());
        let disj_syll_violation = Abnormality::disj_syll_violation(p.clone(), q.clone());

        assert_eq!(contradiction, Abnormality::Contradiction(p.clone()));
        assert_eq!(
            disj_syll_violation,
            Abnormality::DisjunctiveSyllogismViolation(p.clone(), q.clone())
        );
    }

    #[test]
    fn test_abnormality_to_formula() {
        let p = Formula::var("P");
        let q = Formula::var("Q");

        // Test contradiction
        let contradiction = Abnormality::contradiction(p.clone());
        let formula = contradiction.to_formula();
        let expected = Formula::conj(p.clone(), Formula::neg(p.clone()));
        assert_eq!(formula, expected);

        // Test disjunctive syllogism violation
        let ds_violation = Abnormality::disj_syll_violation(p.clone(), q.clone());
        let formula = ds_violation.to_formula();

        let expected = Formula::conj(
            Formula::disj(p.clone(), q.clone()),
            Formula::conj(Formula::neg(p.clone()), Formula::neg(q.clone())),
        );
        assert_eq!(formula, expected);
    }

    #[test]
    fn test_detect_contradiction() {
        let p = Formula::var("P");
        let not_p = Formula::neg(p.clone());

        // Direct contradiction
        let contradiction = Formula::conj(p.clone(), not_p.clone());
        let result = Abnormality::is_abnormality(&contradiction);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), Abnormality::Contradiction(p.clone()));

        // Reverse order
        let contradiction = Formula::conj(not_p.clone(), p.clone());
        let result = Abnormality::is_abnormality(&contradiction);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), Abnormality::Contradiction(p.clone()));

        // Not a contradiction
        let q = Formula::var("Q");
        let not_q = Formula::neg(q.clone());
        let not_contradiction = Formula::conj(p.clone(), not_q.clone());
        let result = Abnormality::is_abnormality(&not_contradiction);
        assert!(result.is_none());
    }

    #[test]
    fn test_detect_ds_violation() {
        let p = Formula::var("P");
        let q = Formula::var("Q");
        let p_or_q = Formula::disj(p.clone(), q.clone());
        let not_p = Formula::neg(p.clone());
        let not_q = Formula::neg(q.clone());

        // Direct DS violation: (P ∨ Q) ∧ ¬P ∧ ¬Q
        let ds_violation =
            Formula::conj(p_or_q.clone(), Formula::conj(not_p.clone(), not_q.clone()));

        let result = Abnormality::is_disj_syll_violation(&ds_violation);
        assert!(result.is_some());
        let (a, b) = result.unwrap();
        assert!(
            (a == p && b == q) || (a == q && b == p),
            "Expected P and Q as the disjuncts, got {:?} and {:?}",
            a,
            b
        );

        // More complex form: ((P ∨ Q) ∧ ¬P) ∧ ¬Q
        let complex_ds = Formula::conj(Formula::conj(p_or_q.clone(), not_p.clone()), not_q.clone());

        let result = Abnormality::is_disj_syll_violation(&complex_ds);
        assert!(result.is_some());
    }

    #[test]
    fn test_check_contradiction() {
        let p = Formula::var("P");
        let not_p = Formula::neg(p.clone());

        // Should detect contradiction
        let result = Abnormality::check_contradiction(&p, &not_p);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), Abnormality::Contradiction(p.clone()));

        // Reverse order should also work
        let result = Abnormality::check_contradiction(&not_p, &p);
        assert!(result.is_some());
        assert_eq!(result.unwrap(), Abnormality::Contradiction(p.clone()));

        // Different formulas should not be a contradiction
        let q = Formula::var("Q");
        let result = Abnormality::check_contradiction(&p, &q);
        assert!(result.is_none());
    }

    #[test]
    fn test_find_potential_ds_violations() {
        let p = Formula::var("P");
        let q = Formula::var("Q");
        let p_or_q = Formula::disj(p.clone(), q.clone());
        let not_p = Formula::neg(p.clone());
        let not_q = Formula::neg(q.clone());

        // Formulas that should form a DS violation
        let formulas = vec![p_or_q.clone(), not_p.clone(), not_q.clone()];

        let result = Abnormality::find_potential_ds_violations(&formulas);
        assert_eq!(result.len(), 1);

        let expected = Abnormality::disj_syll_violation(p.clone(), q.clone());
        assert!(result.contains(&expected));

        // Formulas that don't form a DS violation
        let formulas = vec![p_or_q.clone(), not_p.clone()]; // Missing ¬Q
        let result = Abnormality::find_potential_ds_violations(&formulas);
        assert_eq!(result.len(), 0);
    }

    #[test]
    fn test_detect_abnormalities() {
        let p = Formula::var("P");
        let q = Formula::var("Q");
        let r = Formula::var("R");

        // Create a complex formula with multiple abnormalities
        // (P ∨ Q) ∧ ¬P ∧ ¬Q ∧ (R ∧ ¬R)

        let p_or_q = Formula::disj(p.clone(), q.clone());
        let not_p = Formula::neg(p.clone());
        let not_q = Formula::neg(q.clone());
        let r_and_not_r = Formula::conj(r.clone(), Formula::neg(r.clone()));

        let ds_violation =
            Formula::conj(p_or_q.clone(), Formula::conj(not_p.clone(), not_q.clone()));

        let complex = Formula::conj(ds_violation, r_and_not_r.clone());

        // Detect all abnormalities
        let abnormalities = Abnormality::detect_abnormalities(&complex);

        // Should detect both types of abnormalities
        assert_eq!(abnormalities.len(), 2);

        let expected_ds = Abnormality::disj_syll_violation(p.clone(), q.clone());
        let expected_contradiction = Abnormality::contradiction(r.clone());

        assert!(abnormalities.contains(&expected_ds));
        assert!(abnormalities.contains(&expected_contradiction));
    }
}
