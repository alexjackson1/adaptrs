mod abnormality;
mod formula;
mod lll;
mod parser;
mod proof;
mod strategy;
mod verifier;

// Re-export key components for library users
pub use abnormality::{Abnormality, AbnormalitySet};
pub use formula::Formula;
pub use parser::{
    parse_abnormality, parse_formula, parse_justification, parse_proof, parse_proof_line,
    parse_rule,
};
pub use proof::{Justification, Proof, ProofLine, Rule};
pub use strategy::AdaptiveStrategy;
pub use verifier::{
    get_derivable_formulas, is_formula_derivable, verify_proof, VerificationResult,
};
