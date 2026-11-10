# Lean proofs

    lake exe cache get   # with `third_party/openai-machine` and `FormalizationKit` included
    lake build OnePigeonhole TransposeBase
    lake env lean OnePigeonhole/Audit.lean
    lake env lean OnePigeonhole/ClosureCheck.lean
    lake env lean Audit.lean
    lake build UncrossingWires
    lake env lean UncrossingWires/Audit.lean
    lake env lean UncrossingWires/ClosureCheck.lean
    lake build DominantStrings
    lake env lean DominantStrings/Audit.lean
    lake env lean DominantStrings/ClosureCheck.lean

This project is shared by the papers in `../papers`. `OnePigeonhole/` is the proof of `../papers/one-pigeonhole`, and Section 9 of that paper maps it to the text. `UncrossingWires/` is the proof of `../papers/uncrossing-wires`; see [`UncrossingWires/README.md`](UncrossingWires/README.md). `DominantStrings/` is the proof of `../papers/dominant-strings`; see [`DominantStrings/README.md`](DominantStrings/README.md).

All use three shared libraries. `TransposeBase` holds the word language, the network of a formula, the machine, the end statements in `TransposeBase/Statements.lean`, and the lower bounds `exact_degree`, `cut_prop` and `digit_cost` that the first paper cites. `SatBase` provides the normalization and the branching tree. `FormalizationKit` provides resource bounds on the machine. `Audit.lean` reports the axioms of the shared results that the papers cite.

## How to read the statements

`Audit.lean` reports the axioms. When you read a statement, read the quantifier order: in `pseudo_main` the program `P` comes before `n` and `F`, so it does not depend on the input.

## Formalized and not formalized

Section 9 of `../papers/one-pigeonhole/paper.pdf` and Section 8 of `../papers/uncrossing-wires/paper.pdf` and of `../papers/dominant-strings/paper.pdf` map each paper to the Lean statements and list the differences.
