# The proof with dominant strings

The proof of `../../papers/dominant-strings`. Section 8 of the paper maps it to the text.

| Module | Main declarations |
|---|---|
| `Cube` | `cube`, `viewL`: finite families of numbers, and reading them from one number |
| `Seed` | `Ppol_add`, `seed_rows`, `seed_cols`, `seed_sum`, `sum_cheap`, `dLen_cheap_le`: one rectangle, the letters `P`, `Q`, `R` and the special letter, the dominant strings and their index |
| `Mark` | `mk_eq`, `mk_split`, `mk_viewL`, `sum_mk_index`, `sum_pair_prod`: difference marks of bundles of wires |
| `Step` | `val`, `marks`, `Lev.newW`, `Lev.segT`, `Lev.stepF`, `step_val`: one level with difference marks |
| `Potential` | `sq_two_widths`, `potential_two`, `potential_min`, `newW_total_le`, `ends_row_sq_le`, `ends_all_sq_le` |
| `Chain` | `chain_val`: the chain of levels |
| `Base` | `valEq`, `flipF`, `val_flip`, `BaseNet.val_base`: the network of a formula with equality tests, and its flip to difference marks |
| `Greedy` | `load_table_le`, `psi_table_le_all`, `psi_table_le`: the placement |
| `Pseudo/Prog` | all programs |
| `Pseudo/RectSpec`, `StepSpec`, `BaseSpec`, `GreedySpec`, `CoreSpec` | value and cost of the programs; `core_spec` |
| `Pseudo/FinalLeaf`, `Pseudo/Bounded` | `leaf_main`, `pseudo_bounded`: formulas with few occurrences, no branching |
| `Machine/Bounded` | `occ_toCNF`, `machine_bounded`: the multitape machine for formulas with few occurrences |
| `Statements` | `PseudoBounded`, `RunsWithinBounded`, `MachineBounded`: the end statements of the paper |
| `Pseudo/Final`, `Machine/FinalMain` | `pseudo_main`, `pseudo_wide`, `machine_main`, `not_ETH`: the same chain with the branching tree of `SatBase` |

    lake build DominantStrings TransposeBase
    lake env lean DominantStrings/Audit.lean
    lake env lean DominantStrings/ClosureCheck.lean

`Audit.lean` reports the axioms, and it checks by `rfl` that the end statements are those of `DominantStrings/Statements.lean`
and `TransposeBase/Statements.lean`. `ClosureCheck.lean` shows that `machine_bounded` does not depend on the branching tree.
`ProgTest.lean` runs the program on tiny networks against brute force. It is not part of the proof, and nothing imports it.

The first-level tables are bound as words. A later level has a constant number of nodes, so its weights are recomputed by
nested expressions from the code of the chain, and this costs a constant factor. The library uses `TransposeBase` and
`SatBase` for the word language, helpers for brute force, binomials and fields, the network of a formula, the branching
tree and the arithmetic choice of its parameter, and the machine layer, and `FormalizationKit` for resource bounds on the
machine.
