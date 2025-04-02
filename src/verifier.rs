use crate::proof::{Proof, Justification};
use crate::lower_limit_logic::LowerLimitLogic;
use crate::formula::Formula;

/// Result of proof verification
#[derive(Debug)]
pub struct VerificationResult {
    /// Whether the proof is valid
    pub valid: bool,
    /// Detailed information about the verification, including errors
    pub details: Vec<String>,
}

/// Verifies a proof according to the rules of adaptive logic
pub fn verify_proof(proof: &mut Proof) -> VerificationResult {
    let mut result = VerificationResult {
        valid: true,
        details: Vec::new(),
    };

    // Check each line of the proof
    for i in 0..proof.lines.len() {
        let line = &proof.lines[i];
        let line_num = line.line_number;

        match &line.justification {
            Justification::Premise => {
                // Premises are always valid
                result.details.push(format!("Line {}: Valid premise", line_num));
            },
            Justification::RuleApplication { rule, from_lines } => {
                // Check that all referenced lines exist and precede current line
                for &from_line in from_lines {
                    if from_line >= line_num || proof.get_line(from_line).is_none() {
                        result.valid = false;
                        result.details.push(format!(
                            "Line {}: References non-existent or future line {}",
                            line_num, from_line
                        ));
                        continue;
                    }
                }

                // Check that the rule application is valid
                let rule_result = LowerLimitLogic::apply_rule(proof, rule.clone(), from_lines);
                
                match rule_result {
                    Some((expected_formula, expected_conditions)) => {
                        // Check that the derived formula matches the expected one
                        if line.formula != expected_formula {
                            result.valid = false;
                            result.details.push(format!(
                                "Line {}: Formula does not match derivation. Expected: {}, Found: {}",
                                line_num, expected_formula, line.formula
                            ));
                        }
                        
                        // Check that the conditions match the expected ones
                        if line.conditions != expected_conditions {
                            result.valid = false;
                            result.details.push(format!(
                                "Line {}: Conditions do not match derivation",
                                line_num
                            ));
                        }
                        
                        if line.formula == expected_formula && line.conditions == expected_conditions {
                            result.details.push(format!(
                                "Line {}: Valid application of rule {:?}",
                                line_num, rule
                            ));
                        }
                    },
                    None => {
                        result.valid = false;
                        result.details.push(format!(
                            "Line {}: Invalid application of rule {:?}",
                            line_num, rule
                        ));
                    }
                }
            }
        }
    }

    // Apply marking according to the adaptive strategy
    proof.apply_marking();
    
    // Check which lines are marked
    for line in &proof.lines {
        if line.marked {
            result.details.push(format!(
                "Line {}: Marked as invalid due to abnormalities",
                line.line_number
            ));
        }
    }

    result
}

/// Gets all derivable formulas from a proof (those that are not marked)
pub fn get_derivable_formulas(proof: &Proof) -> Vec<Formula> {
    proof.lines.iter()
        .filter(|line| !line.marked)
        .map(|line| line.formula.clone())
        .collect()
}

/// Checks if a specific formula is derivable in the proof
pub fn is_formula_derivable(proof: &Proof, formula: &Formula) -> bool {
    proof.lines.iter()
        .any(|line| !line.marked && line.formula == *formula)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::strategy::AdaptiveStrategy;
    use crate::Rule;
    use std::collections::HashSet;

    #[test]
    fn test_verify_simple_proof() {
        let mut proof = Proof::new(AdaptiveStrategy::Reliability);
        
        // 1. P                  PREM
        // 2. Q                  PREM
        // 3. P ∧ Q              1,2 AndIntro
        
        let p = Formula::var("P");
        let q = Formula::var("Q");
        
        let line1 = proof.add_premise(p.clone());
        let line2 = proof.add_premise(q.clone());
        let p_and_q = Formula::conj(p.clone(), q.clone());
        let _line3 = proof.add_line(
            p_and_q.clone(), 
            Rule::AndIntro, 
            vec![line1, line2], 
            HashSet::new()
        );
        
        let result = verify_proof(&mut proof);
        assert!(result.valid);
        
        let derivable = get_derivable_formulas(&proof);
        assert!(derivable.contains(&p));
        assert!(derivable.contains(&q));
        assert!(derivable.contains(&p_and_q));
    }

    #[test]
    fn test_verify_with_disjunctive_syllogism() {
        let mut proof = Proof::new(AdaptiveStrategy::Reliability);
        
        // 1. P ∨ Q              PREM
        // 2. ¬P                 PREM
        // 3. Q                  1,2 DisjSyll {(P ∨ Q) ∧ ¬P ∧ ¬Q}
        
        let p = Formula::var("P");
        let q = Formula::var("Q");
        let p_or_q = Formula::disj(p.clone(), q.clone());
        let not_p = Formula::neg(p.clone());
        
        let line1 = proof.add_premise(p_or_q.clone());
        let line2 = proof.add_premise(not_p.clone());
        
        // We need to manually create the abnormality for this test
        let mut conditions = HashSet::new();
        let abnormality = crate::abnormality::Abnormality::disj_syll_violation(
            p.clone(), 
            q.clone()
        );
        conditions.insert(abnormality);
        
        let _line3 = proof.add_line(
            q.clone(), 
            Rule::DisjSyll, 
            vec![line1, line2], 
            conditions
        );
        
        let result = verify_proof(&mut proof);
        
        // The proof should be valid, but Q might be marked depending on the strategy
        assert!(result.valid);
    }
}