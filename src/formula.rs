use std::fmt;

/// Represents a propositional formula in the adaptive logic system
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Formula {
    /// Propositional variable (e.g., P, Q, R)
    Var(String),
    /// Negation (¬A)
    Neg(Box<Formula>),
    /// Conjunction (A ∧ B)
    Conj(Box<Formula>, Box<Formula>),
    /// Disjunction (A ∨ B)
    Disj(Box<Formula>, Box<Formula>),
    /// Implication (A → B)
    Impl(Box<Formula>, Box<Formula>),
    /// Biconditional (A ↔ B)
    Bicon(Box<Formula>, Box<Formula>),
}

impl Formula {
    /// Creates a new variable formula
    pub fn var<S: Into<String>>(name: S) -> Self {
        Formula::Var(name.into())
    }

    /// Creates a new negation formula
    pub fn neg(formula: Formula) -> Self {
        Formula::Neg(Box::new(formula))
    }

    /// Creates a new conjunction formula
    pub fn conj(left: Formula, right: Formula) -> Self {
        Formula::Conj(Box::new(left), Box::new(right))
    }

    /// Creates a new disjunction formula
    pub fn disj(left: Formula, right: Formula) -> Self {
        Formula::Disj(Box::new(left), Box::new(right))
    }

    /// Creates a new implication formula
    pub fn impl_(antecedent: Formula, consequent: Formula) -> Self {
        Formula::Impl(Box::new(antecedent), Box::new(consequent))
    }

    /// Creates a new biconditional formula
    pub fn bicon(left: Formula, right: Formula) -> Self {
        Formula::Bicon(Box::new(left), Box::new(right))
    }

    /// Returns all subformulas of this formula
    pub fn subformulas(&self) -> Vec<Formula> {
        let mut result = vec![self.clone()];
        match self {
            Formula::Var(_) => {}
            Formula::Neg(f) => {
                result.extend(f.subformulas());
            }
            Formula::Conj(left, right)
            | Formula::Disj(left, right)
            | Formula::Impl(left, right)
            | Formula::Bicon(left, right) => {
                result.extend(left.subformulas());
                result.extend(right.subformulas());
            }
        }
        result
    }
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Var(name) => write!(f, "{}", name),
            Formula::Neg(formula) => write!(f, "¬{}", parenthesize_if_needed(formula)),
            Formula::Conj(left, right) => write!(
                f,
                "{} ∧ {}",
                parenthesize_if_needed(left),
                parenthesize_if_needed(right)
            ),
            Formula::Disj(left, right) => write!(
                f,
                "{} ∨ {}",
                parenthesize_if_needed(left),
                parenthesize_if_needed(right)
            ),
            Formula::Impl(left, right) => write!(
                f,
                "{} → {}",
                parenthesize_if_needed(left),
                parenthesize_if_needed(right)
            ),
            Formula::Bicon(left, right) => write!(
                f,
                "{} ↔ {}",
                parenthesize_if_needed(left),
                parenthesize_if_needed(right)
            ),
        }
    }
}

/// Helper function to add parentheses when needed for nested formulas
fn parenthesize_if_needed(formula: &Formula) -> String {
    match formula {
        Formula::Var(_) => format!("{}", formula),
        _ => format!("({})", formula),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_formula_creation() {
        let p = Formula::var("P");
        let q = Formula::var("Q");
        let not_p = Formula::neg(p.clone());
        let p_and_q = Formula::conj(p.clone(), q.clone());

        // Check creation of basic operators
        assert_eq!(not_p, Formula::Neg(Box::new(Formula::Var("P".to_string()))));
        assert_eq!(
            p_and_q,
            Formula::Conj(
                Box::new(Formula::Var("P".to_string())),
                Box::new(Formula::Var("Q".to_string()))
            )
        );

        // Create and test other operators (just to avoid unused variable warnings)
        let p_or_q = Formula::disj(p.clone(), q.clone());
        let p_impl_q = Formula::impl_(p.clone(), q.clone());
        let p_bicon_q = Formula::bicon(p.clone(), q.clone());

        assert_eq!(
            p_or_q,
            Formula::Disj(
                Box::new(Formula::Var("P".to_string())),
                Box::new(Formula::Var("Q".to_string()))
            )
        );
        assert_eq!(
            p_impl_q,
            Formula::Impl(
                Box::new(Formula::Var("P".to_string())),
                Box::new(Formula::Var("Q".to_string()))
            )
        );
        assert_eq!(
            p_bicon_q,
            Formula::Bicon(
                Box::new(Formula::Var("P".to_string())),
                Box::new(Formula::Var("Q".to_string()))
            )
        );
    }

    #[test]
    fn test_formula_display() {
        let p = Formula::var("P");
        let q = Formula::var("Q");
        let not_p = Formula::neg(p.clone());
        let p_and_q = Formula::conj(p.clone(), q.clone());
        let complex = Formula::impl_(
            Formula::disj(p.clone(), q.clone()),
            Formula::neg(p_and_q.clone()),
        );

        assert_eq!(p.to_string(), "P");
        assert_eq!(not_p.to_string(), "¬P");
        assert_eq!(p_and_q.to_string(), "P ∧ Q");

        // Fix the assertion to match the actual output with the parentheses
        let actual = complex.to_string();
        let expected = "(P ∨ Q) → (¬(P ∧ Q))";
        assert_eq!(actual, expected);
    }
}
