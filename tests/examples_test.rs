use adaptrs::{parse_proof, verify_proof, AdaptiveStrategy};
use std::fs;
use std::path::Path;

#[test]
fn test_simple_proof_example() {
    let content = fs::read_to_string("examples/simple_proof.txt").unwrap();
    let mut proof = parse_proof(&content, AdaptiveStrategy::Reliability).unwrap();
    let result = verify_proof(&mut proof);
    assert!(result.valid, "simple_proof.txt should be valid");
}

#[test]
fn test_marked_proof_example() {
    let content = fs::read_to_string("examples/marked_proof.txt").unwrap();
    let mut proof = parse_proof(&content, AdaptiveStrategy::Reliability).unwrap();
    let result = verify_proof(&mut proof);
    assert!(result.valid, "marked_proof.txt should be valid");

    // In this proof, the last line should be marked
    assert!(
        proof.lines.last().unwrap().marked,
        "Last line in marked_proof.txt should be marked"
    );
}

#[test]
fn test_complex_proof_example() {
    let content = fs::read_to_string("examples/complex_proof.txt").unwrap();
    let mut proof = parse_proof(&content, AdaptiveStrategy::Reliability).unwrap();
    let result = verify_proof(&mut proof);
    assert!(result.valid, "complex_proof.txt should be valid");
}

#[test]
fn test_modus_ponens_proof_example() {
    let content = fs::read_to_string("examples/modus_ponens_proof.txt").unwrap();
    let mut proof = parse_proof(&content, AdaptiveStrategy::Reliability).unwrap();
    let result = verify_proof(&mut proof);
    assert!(result.valid, "modus_ponens_proof.txt should be valid");
}

#[test]
fn test_all_example_files_with_both_strategies() {
    let examples_dir = Path::new("examples");
    if examples_dir.exists() && examples_dir.is_dir() {
        let entries = fs::read_dir(examples_dir).unwrap();

        for entry in entries {
            let entry = entry.unwrap();
            let path = entry.path();

            // Only process .txt files
            if path.extension().map_or(false, |ext| ext == "txt") {
                let content = fs::read_to_string(&path).unwrap();
                let file_name = path.file_name().unwrap().to_string_lossy();

                // Test with Reliability strategy
                let mut proof_rel = parse_proof(&content, AdaptiveStrategy::Reliability).unwrap();
                let result_rel = verify_proof(&mut proof_rel);
                assert!(
                    result_rel.valid,
                    "{} should be valid with Reliability strategy",
                    file_name
                );

                // Test with Minimal Abnormality strategy
                let mut proof_min =
                    parse_proof(&content, AdaptiveStrategy::MinimalAbnormality).unwrap();
                let result_min = verify_proof(&mut proof_min);
                assert!(
                    result_min.valid,
                    "{} should be valid with Minimal Abnormality strategy",
                    file_name
                );
            }
        }
    }
}
