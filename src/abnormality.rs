use std::collections::HashSet;
use std::fmt;
use crate::formula::Formula;

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
            },
            Abnormality::Contradiction(a) => {
                Formula::conj(a.clone(), Formula::neg(a.clone()))
            }
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
        // This is more complex and would require further pattern matching
        // For now, this will be a placeholder for the full implementation
        None
    }
}

impl fmt::Display for Abnormality {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Abnormality::DisjunctiveSyllogismViolation(a, b) => {
                write!(f, "({} ∨ {}) ∧ ¬{} ∧ ¬{}", a, b, a, b)
            },
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
        assert_eq!(disj_syll_violation, Abnormality::DisjunctiveSyllogismViolation(p.clone(), q.clone()));
    }

    #[test]
    fn test_abnormality_to_formula() {
        let p = Formula::var("P");
        
        let contradiction = Abnormality::contradiction(p.clone());
        let formula = contradiction.to_formula();
        
        let expected = Formula::conj(p.clone(), Formula::neg(p.clone()));
        assert_eq!(formula, expected);
    }
}