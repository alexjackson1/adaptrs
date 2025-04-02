use crate::abnormality::AbnormalitySet;
use crate::formula::Formula;
use crate::strategy::AdaptiveStrategy;
use std::collections::HashSet;
use std::fmt;

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

    // Conditional Rules
    /// Disjunctive syllogism: A ∨ B, ¬A ⊢ B
    DisjSyll,
    /// Ex falso quodlibet: A ∧ ¬A ⊢ B
    ExFalso,
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rule::Prem => write!(f, "PREM"),
            Rule::AndIntro => write!(f, "∧I"),
            Rule::AndElim1 => write!(f, "∧E1"),
            Rule::AndElim2 => write!(f, "∧E2"),
            Rule::OrIntro1 => write!(f, "∨I1"),
            Rule::OrIntro2 => write!(f, "∨I2"),
            Rule::ModusPonens => write!(f, "MP"),
            Rule::ModusTollens => write!(f, "MT"),
            Rule::DisjSyll => write!(f, "DS"),
            Rule::ExFalso => write!(f, "EFQ"),
        }
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
            write!(f, " ✓")?;
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
}

impl Proof {
    /// Creates a new empty proof with the given strategy
    pub fn new(strategy: AdaptiveStrategy) -> Self {
        Proof {
            lines: Vec::new(),
            strategy,
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
