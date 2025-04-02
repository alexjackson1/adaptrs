mod formula;
mod parser;
mod proof;
mod lower_limit_logic;
mod abnormality;
mod strategy;
mod verifier;

// Re-export key components for library users
pub use formula::Formula;
pub use proof::{Proof, ProofLine, Justification, Rule};
pub use abnormality::{Abnormality, AbnormalitySet};
pub use strategy::AdaptiveStrategy;
pub use verifier::{verify_proof, get_derivable_formulas, is_formula_derivable, VerificationResult};
pub use parser::{parse_formula, parse_proof, parse_rule, parse_abnormality, parse_justification, parse_proof_line};