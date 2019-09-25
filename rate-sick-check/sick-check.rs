//! Verify SICK certificates of proof incorrectness produced by rate

use clap::Arg;
use std::io::Read;
use toml;

use rate_common::{
    assignment::{stable_under_unit_propagation, Assignment},
    clause::{Reason, RedundancyProperty},
    comment, die,
    literal::Literal,
    memory::{Array, Vector},
    output::{install_signal_handler, print_solution},
    parser::{
        clause_db, open_file, proof_format_by_extension, run_parser, witness_db,
        BinaryMode, FixedSizeHashTable, HashTable, Parser, ProofSyntax,
    },
    requires,
    sick::Sick,
    write_to_stdout,
};

#[allow(clippy::cognitive_complexity)]
fn main() -> Result<(), ()> {
    install_signal_handler();
    let app = clap::App::new("sick-check")
        .version(env!("CARGO_PKG_VERSION"))
        .about("Verify SICK certificates stating why a DRAT proof is incorrect")
        .arg(
            Arg::with_name("INPUT")
                .required(true)
                .help("input file in DIMACS format"),
        )
        .arg(
            Arg::with_name("PROOF")
                .required(true)
                .help("proof file in DRAT format"),
        )
        .arg(
            Arg::with_name("CERTIFICATE")
                .required(true)
                .help("falsifying certificate file in SICK format"),
        );
    let matches = app.get_matches();
    let formula_filename = matches.value_of("INPUT").unwrap();
    let proof_filename = matches.value_of("PROOF").unwrap();
    let sick_filename = matches.value_of("CERTIFICATE").unwrap();
    let proof_file_redundancy_property = proof_format_by_extension(proof_filename);

    let mut toml_str = String::new();
    let mut sick_file = open_file(sick_filename);
    sick_file
        .read_to_string(&mut toml_str)
        .unwrap_or_else(|err| die!("Failed to read SICK file: {}", err));
    let sick: Sick =
        toml::from_str(&toml_str).unwrap_or_else(|err| die!("Failed to parse SICK file: {}", err));
    let redundancy_property = match sick.proof_format.as_ref() {
        "DRAT-arbitrary-pivot" => RedundancyProperty::RAT,
        "DRAT-pivot-is-first-literal" => RedundancyProperty::RAT,
        "PR" => RedundancyProperty::PR,
        format => die!("Unsupported proof format: {}", format),
    };
    requires!(redundancy_property == proof_file_redundancy_property);
    let mut clause_ids = FixedSizeHashTable::new();
    let mut parser = Parser::new(ProofSyntax::Drat);        // todo: change this into option
    parser.max_proof_steps = Some(sick.proof_step);
    run_parser(
        &mut parser,
        formula_filename,
        proof_filename,
        BinaryMode::DratTrim,
        &mut clause_ids,
    );

    if sick.proof_step > parser.proof.len() {
        die!(
            "Specified proof step exceeds proof size: {}",
            sick.proof_step
        );
    }
    let lemma = parser.proof[sick.proof_step - 1].clause();
    requires!(lemma.index < clause_db().number_of_clauses());
    let mut assignment = Assignment::new(parser.maxvar);
    for &literal in &sick.natural_model {
        if assignment[-literal] {
            die!(
                "Natural model is inconsistent in variable {}",
                literal.variable()
            );
        }
        assignment.push(literal, Reason::assumed());
    }
    if clause_db().clause(lemma).is_empty() {
        comment!("Tried to introduce empty clause but natural model is consistent");
        print_solution("VERIFIED");
        return Ok(());
    }
    let natural_model_length = assignment.len();

    for &literal in clause_db().clause(lemma) {
        if !assignment[-literal] {
            die!("Natural model does not falsify lemma literal {}", literal);
        }
    }
    // Delete the lemma, so it is not considered to be part of the formula.
    clause_ids.delete_clause(lemma);
    for &clause in &clause_ids {
        if clause < lemma && !stable_under_unit_propagation(&assignment, clause_db().clause(clause))
        {
            die!(
                "Natural model is not the shared UP-model for clause {}",
                clause_db().clause_to_string(clause)
            );
        }
    }
    let witnesses = sick.witness.unwrap_or_else(Vector::new);
    const PIVOT: &str = "RAT requires to specify a pivot for each witness";
    if redundancy_property == RedundancyProperty::RAT {
        let mut specified_pivots: Vec<Literal> = witnesses
            .iter()
            .map(|witness| witness.pivot.expect(PIVOT))
            .collect();
        let mut expected_pivots: Vec<Literal> = clause_db()
            .clause(lemma)
            .iter()
            .filter(|&&l| l != Literal::BOTTOM)
            .cloned()
            .collect();
        if !specified_pivots.is_empty() {
            match sick.proof_format.as_ref() {
                "DRAT-arbitrary-pivot" => {
                    specified_pivots.sort();
                    expected_pivots.sort();
                    if specified_pivots != expected_pivots {
                        die!("Using proof_format = \"{}\": you need exactly one counterexample for each pivot in the lemma\nlemma: {}\npivots: {}",
                        sick.proof_format,
                        expected_pivots.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(" "),
                        specified_pivots.iter().map(|l| format!("{}", l)).collect::<Vec<_>>().join(" "),
                        )
                    }
                }
                "DRAT-pivot-is-first-literal" => {
                    if specified_pivots.len() > 1 {
                        die!("Using proof_format = \"{}\", the first literal must be specified as pivot and nothing else",
                        sick.proof_format);
                    }
                }
                _ => unreachable!(),
            };
        }
    }
    for witness in witnesses {
        clause_db().open_clause();
        for &literal in &witness.failing_clause {
            clause_db().push_literal(literal);
        }
        clause_db().push_literal(Literal::new(0));
        let failing_clause_tmp = clause_db().last_clause();
        let failing_clause = clause_ids
            .find_equal_clause(failing_clause_tmp, /*delete=*/ false)
            .unwrap_or_else(|| {
                die!(
                    "Failing clause is not present in the formula: {}",
                    clause_db().clause_to_string(failing_clause_tmp)
                );
            });
        clause_db().pop_clause();
        let lemma_slice = clause_db().clause(lemma);
        for &literal in &witness.failing_model {
            if assignment[-literal] {
                die!(
                    "Failing model is inconsistent in variable {}",
                    literal.variable()
                );
            }
            assignment.push(literal, Reason::assumed());
        }
        let resolvent: Vec<Literal> = match redundancy_property {
            RedundancyProperty::RAT => {
                let pivot = witness.pivot.expect(PIVOT);
                lemma_slice
                    .iter()
                    .chain(witness.failing_clause.iter())
                    .filter(|&&lit| lit.variable() != pivot.variable())
                    .cloned()
                    .collect()
            }
            RedundancyProperty::PR => {
                let mut literal_is_in_witness =
                    Array::new(false, parser.maxvar.array_size_for_literals());
                for &literal in witness_db().witness(lemma) {
                    literal_is_in_witness[literal] = true;
                }
                if witness
                    .failing_clause
                    .iter()
                    .any(|&lit| literal_is_in_witness[lit])
                {
                    die!(
                        "Reduct of failing clause {} is satisified under witness {}",
                        clause_db().clause_to_string(failing_clause),
                        witness_db().witness_to_string(failing_clause)
                    )
                }
                lemma_slice
                    .iter()
                    .chain(
                        witness
                            .failing_clause
                            .iter()
                            .filter(|&&lit| !literal_is_in_witness[-lit]),
                    )
                    .cloned()
                    .collect()
            }
        };
        for &literal in &resolvent {
            if !assignment[-literal] {
                die!(
                    "Failing model does not falsify resolvent literal {}",
                    literal
                );
            }
        }
        for &clause in &clause_ids {
            if clause < lemma
                && !stable_under_unit_propagation(&assignment, clause_db().clause(clause))
            {
                die!(
                    "Failing model is not the shared UP-model for clause {}",
                    clause_db().clause_to_string(clause)
                );
            }
        }
        while assignment.len() > natural_model_length {
            assignment.pop();
        }
    }
    print_solution("VERIFIED");
    Ok(())
}
