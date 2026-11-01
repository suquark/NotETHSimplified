# The proof by uncrossing wires

The proof of `../../papers/uncrossing-wires`. Section 8 of the paper maps it to the text.

| Module | Main declarations |
|---|---|
| `Cube` | `cube`, `viewL`: finite families of numbers, and reading them from one number |
| `Seed` | `Ppol_add`, `seed_rows`, `seed_cols`, `seed_sum`, `dLen_cheap_le`: one rectangle |
| `Step` | `val`, `Lev.newW`, `Lev.stepF`, `step_val`: one step |
| `Potential` | `potential_two`, `potential_min`, `newW_total_le`, `ends_row_sq_le`, `ends_all_sq_le` |
| `Chain` | `chain_val`: the chain of steps |
| `Base` | `BaseNet.val_base`: a network of `TransposeBase` as a first level |
| `Greedy` | `load_table_le`, `psi_table_le_all`, `psi_table_le`: the placement |
| `Pseudo/Prog` | all programs |
| `Pseudo/RectSpec`, `StepSpec`, `BaseSpec`, `GreedySpec`, `CoreSpec` | value and cost of the programs; `core_spec` |
| `Pseudo/FinalLeaf`, `Pseudo/Final` | `leaf_main`, `pseudo_main`, `pseudo_wide` |
| `Machine/FinalMain` | `machine_main`, `eth_false`, `not_ETH` |

    lake build UncrossingWires TransposeBase
    lake env lean UncrossingWires/Audit.lean
    lake env lean UncrossingWires/ClosureCheck.lean

`Audit.lean` reports the axioms, and it checks by `rfl` that the end statements are those of `TransposeBase/Statements.lean`.
`ProgTest.lean` runs the program on tiny networks against brute force. It is not part of the proof, and nothing imports it.

The first-level tables are bound as words. A later level has a constant number of nodes, so its weights are recomputed by nested expressions from the code of the chain, and this costs a constant factor.
It uses `TransposeBase` and `SatBase` for the word language, helpers for brute force, binomials and fields, the network of a formula, the branching tree and the arithmetic choice of its parameter, and the machine layer, and `FormalizationKit` for resource bounds on the machine.
