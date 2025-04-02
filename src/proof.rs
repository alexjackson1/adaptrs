use crate::abnormality::{Abnormality, AbnormalitySet};
use crate::formula::Formula;
use crate::strategy::AdaptiveStrategy;
use std::collections::HashSet;
use std::fmt;

/// Trait for defining how rules of inference behave in adaptive logic
pub trait LogicRule {
    /// Returns the type of the rule (Premise, Unconditional, or Conditional)
    fn rule_type(&self) -> RuleType;

    /// Returns the name or symbol for the rule
    fn name(&self) -> &'static str;

    /// Returns a description of the rule in logical notation
    fn description(&self) -> &'static str;

    /// Returns the minimum number of premises needed for this rule
    fn min_premises(&self) -> usize;

    /// Returns the maximum number of premises allowed for this rule
    fn max_premises(&self) -> usize;
}

/// Future implementation could look like:
///
/// ```ignore
/// enum MyRule {
///     And,
///     Or
/// }
///
/// impl LogicRule for MyRule {
///    fn rule_type(&self) -> RuleType {
///        RuleType::Unconditional
///    }
///    fn name(&self) -> &'static str {
///        match self {
///            MyRule::And => "AND",
///            MyRule::Or => "OR",
///        }
///    }
///    fn description(&self) -> &'static str {
///        "Example rule"
///    }
///    fn min_premises(&self) -> usize {
///        2
///    }
///    fn max_premises(&self) -> usize {
///        2
///    }
/// }
/// ```
/// Represents the type of a rule in adaptive logic
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleType {
    /// PREM: Premise introduction rule
    Premise,
    /// RU: Unconditional rule from the lower limit logic
    Unconditional,
    /// RC: Conditional rule that relies on abnormality assumptions
    Conditional,
}

/// Represents a rule of inference in the adaptive logic system
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rule {
    /// Premise introduction
    Prem,

    // Unconditional Rules (Lower Limit Logic)
    /// Conjunction introduction: A, B ⊢ A ∧ B
    AndIntro,
    /// Conjunction elimination 1: A ∧ B ⊢ A
    AndElim1,
    /// Conjunction elimination 2: A ∧ B ⊢ B
    AndElim2,
    /// Disjunction introduction 1: A ⊢ A ∨ B
    OrIntro1,
    /// Disjunction introduction 2: B ⊢ A ∨ B
    OrIntro2,
    /// Modus ponens: A, A → B ⊢ B
    ModusPonens,
    /// Modus tollens: A → B, ¬B ⊢ ¬A
    ModusTollens,
    /// Contrapositive equivalence: P → Q ⊢ ¬Q → ¬P
    ContrapositiveEquiv,
    /// Double negation introduction: P ⊢ ¬¬P
    DoubleNegIntro,
    /// Double negation elimination: ¬¬P ⊢ P
    DoubleNegElim,

    // Conditional Rules
    /// Disjunctive syllogism: A ∨ B, ¬A ⊢ B
    DisjSyll,
    /// Ex falso quodlibet: A ∧ ¬A ⊢ B
    ExFalso,
}

impl LogicRule for Rule {
    fn rule_type(&self) -> RuleType {
        match self {
            Rule::Prem => RuleType::Premise,

            // Unconditional rules (part of lower limit logic)
            Rule::AndIntro
            | Rule::AndElim1
            | Rule::AndElim2
            | Rule::OrIntro1
            | Rule::OrIntro2
            | Rule::ModusPonens
            | Rule::ModusTollens
            | Rule::ContrapositiveEquiv
            | Rule::DoubleNegIntro
            | Rule::DoubleNegElim => RuleType::Unconditional,

            // Conditional rules (require abnormality assumptions)
            Rule::DisjSyll | Rule::ExFalso => RuleType::Conditional,
        }
    }

    fn name(&self) -> &'static str {
        match self {
            Rule::Prem => "PREM",
            Rule::AndIntro => "∧I",
            Rule::AndElim1 => "∧E1",
            Rule::AndElim2 => "∧E2",
            Rule::OrIntro1 => "∨I1",
            Rule::OrIntro2 => "∨I2",
            Rule::ModusPonens => "MP",
            Rule::ModusTollens => "MT",
            Rule::ContrapositiveEquiv => "CE",
            Rule::DoubleNegIntro => "DNI",
            Rule::DoubleNegElim => "DNE",
            Rule::DisjSyll => "DS",
            Rule::ExFalso => "EFQ",
        }
    }

    fn description(&self) -> &'static str {
        match self {
            Rule::Prem => "Premise introduction",
            Rule::AndIntro => "Conjunction introduction: A, B ⊢ A ∧ B",
            Rule::AndElim1 => "Conjunction elimination 1: A ∧ B ⊢ A",
            Rule::AndElim2 => "Conjunction elimination 2: A ∧ B ⊢ B",
            Rule::OrIntro1 => "Disjunction introduction 1: A ⊢ A ∨ B",
            Rule::OrIntro2 => "Disjunction introduction 2: B ⊢ A ∨ B",
            Rule::ModusPonens => "Modus ponens: A, A → B ⊢ B",
            Rule::ModusTollens => "Modus tollens: A → B, ¬B ⊢ ¬A",
            Rule::ContrapositiveEquiv => "Contrapositive equivalence: P → Q ⊢ ¬Q → ¬P",
            Rule::DoubleNegIntro => "Double negation introduction: P ⊢ ¬¬P",
            Rule::DoubleNegElim => "Double negation elimination: ¬¬P ⊢ P",
            Rule::DisjSyll => "Disjunctive syllogism: A ∨ B, ¬A ⊢ B",
            Rule::ExFalso => "Ex falso quodlibet: A ∧ ¬A ⊢ B",
        }
    }

    fn min_premises(&self) -> usize {
        match self {
            Rule::Prem => 0,
            Rule::AndIntro => 2,
            Rule::AndElim1 => 1,
            Rule::AndElim2 => 1,
            Rule::OrIntro1 => 1,
            Rule::OrIntro2 => 1,
            Rule::ModusPonens => 2, // Standard case requires two premises
            Rule::ModusTollens => 2,
            Rule::ContrapositiveEquiv => 1,
            Rule::DoubleNegIntro => 1,
            Rule::DoubleNegElim => 1,
            Rule::DisjSyll => 2,
            Rule::ExFalso => 2,
        }
    }

    fn max_premises(&self) -> usize {
        match self {
            Rule::Prem => 0,
            Rule::AndIntro => 2,
            Rule::AndElim1 => 1,
            Rule::AndElim2 => 1,
            Rule::OrIntro1 => 2,    // B is optional
            Rule::OrIntro2 => 2,    // A is optional
            Rule::ModusPonens => 2, // Requires exactly 2 premises: A and (A → B)
            Rule::ModusTollens => 2,
            Rule::ContrapositiveEquiv => 1,
            Rule::DoubleNegIntro => 1,
            Rule::DoubleNegElim => 1,
            Rule::DisjSyll => 2,
            Rule::ExFalso => 3, // Up to 2 for contradiction and 1 for conclusion
        }
    }
}

impl Rule {
    /// Returns true if the rule is a premise introduction
    pub fn is_premise(&self) -> bool {
        self.rule_type() == RuleType::Premise
    }

    /// Returns true if the rule is unconditional (RU)
    pub fn is_unconditional(&self) -> bool {
        self.rule_type() == RuleType::Unconditional
    }

    /// Returns true if the rule is conditional (RC)
    pub fn is_conditional(&self) -> bool {
        self.rule_type() == RuleType::Conditional
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Represents a justification for a formula in a proof
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Justification {
    /// Premise
    Premise,
    /// Rule application with line references
    RuleApplication { rule: Rule, from_lines: Vec<usize> },
}

impl fmt::Display for Justification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Justification::Premise => write!(f, "PREM"),
            Justification::RuleApplication { rule, from_lines } => {
                let lines = from_lines
                    .iter()
                    .map(|n| n.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                write!(f, "{} {}", lines, rule)
            }
        }
    }
}

/// Represents a line in a proof
#[derive(Clone, Debug)]
pub struct ProofLine {
    /// Line number in the proof
    pub line_number: usize,
    /// Formula at this line
    pub formula: Formula,
    /// Justification for the formula
    pub justification: Justification,
    /// Set of abnormality conditions
    pub conditions: AbnormalitySet,
    /// Whether the line is marked (invalid)
    pub marked: bool,
}

impl fmt::Display for ProofLine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}. {}\t{}",
            self.line_number, self.formula, self.justification
        )?;

        if !self.conditions.is_empty() {
            let conditions = self
                .conditions
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            write!(f, " {{{}}}", conditions)?;
        }

        if self.marked {
            write!(f, " ✗")?; // Changed to X to indicate the line is marked as invalid
        }

        Ok(())
    }
}

/// Represents a proof in the adaptive logic system
#[derive(Clone, Debug)]
pub struct Proof {
    /// Lines of the proof
    pub lines: Vec<ProofLine>,
    /// Adaptive strategy used
    pub strategy: AdaptiveStrategy,
    /// Abnormalities derived during proof verification
    pub derived_abnormalities: HashSet<Abnormality>,
}

impl Proof {
    /// Creates a new empty proof with the given strategy
    pub fn new(strategy: AdaptiveStrategy) -> Self {
        Proof {
            lines: Vec::new(),
            strategy,
            derived_abnormalities: HashSet::new(),
        }
    }

    /// Adds a premise to the proof
    pub fn add_premise(&mut self, formula: Formula) -> usize {
        let line_number = self.lines.len() + 1;
        let line = ProofLine {
            line_number,
            formula,
            justification: Justification::Premise,
            conditions: HashSet::new(),
            marked: false,
        };
        self.lines.push(line);
        line_number
    }

    /// Adds a derived line to the proof
    pub fn add_line(
        &mut self,
        formula: Formula,
        rule: Rule,
        from_lines: Vec<usize>,
        conditions: AbnormalitySet,
    ) -> usize {
        let line_number = self.lines.len() + 1;
        let line = ProofLine {
            line_number,
            formula,
            justification: Justification::RuleApplication { rule, from_lines },
            conditions,
            marked: false,
        };
        self.lines.push(line);
        line_number
    }

    /// Applies the marking strategy to the proof
    pub fn apply_marking(&mut self) {
        let strategy = self.strategy.clone();
        strategy.apply_marking(self);
    }

    /// Gets a line by its number
    pub fn get_line(&self, line_number: usize) -> Option<&ProofLine> {
        if line_number > 0 && line_number <= self.lines.len() {
            Some(&self.lines[line_number - 1])
        } else {
            None
        }
    }
}

impl fmt::Display for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for line in &self.lines {
            writeln!(f, "{}", line)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::strategy::AdaptiveStrategy;

    #[test]
    fn test_proof_creation() {
        let mut proof = Proof::new(AdaptiveStrategy::Reliability);
        let p = Formula::var("P");
        let q = Formula::var("Q");

        let line1 = proof.add_premise(p.clone());
        let line2 = proof.add_premise(q.clone());
        let p_and_q = Formula::conj(p.clone(), q.clone());
        let line3 = proof.add_line(
            p_and_q.clone(),
            Rule::AndIntro,
            vec![line1, line2],
            HashSet::new(),
        );

        assert_eq!(proof.lines.len(), 3);
        assert_eq!(line3, 3);
        assert_eq!(proof.get_line(1).unwrap().formula, p);
        assert_eq!(proof.get_line(2).unwrap().formula, q);
        assert_eq!(proof.get_line(3).unwrap().formula, p_and_q);
    }
}
