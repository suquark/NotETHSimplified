# Simplified proofs that the Exponential Time Hypothesis fails

This repository has three proofs of one theorem: for each `ε > 0`, 3-SAT on `n` variables is decided deterministically in time `C_ε |φ|^{O_ε(1)} 2^{εn}`, where `|φ|` is the size of the input.

OpenAI and Claude (Anthropic) first announced this theorem. These papers do not aim for a better bound. They aim for proofs that are short, easy to follow, and that show why the argument works. All three are formalized in Lean 4 down to a primitive multitape machine.

| Paper | Key idea | Full paper | Proof only | Lean library |
|---|---|---|---|---|
| [One Pigeonhole for 3-SAT: A Determinant That Removes the Correction](papers/one-pigeonhole) | A determinant vanishes on dependent rows | [13 pages](papers/one-pigeonhole/paper.pdf) | [3 pages](papers/one-pigeonhole/proof.pdf) | `OnePigeonhole` |
| [Uncrossing Wires for 3-SAT: A Potential That Closes the Recursion](papers/uncrossing-wires) | A quadratic potential falls at every level | [13 pages](papers/uncrossing-wires/paper.pdf) | [4 pages](papers/uncrossing-wires/proof.pdf) | `UncrossingWires` |
| [Dominant Strings for 3-SAT: Counting Solutions with Few Occurrences per Variable](papers/dominant-strings) | A wire carries the difference of its bits, so a crossing is `V − H` | [15 pages](papers/dominant-strings/paper.pdf) | [5 pages](papers/dominant-strings/proof.pdf) | `DominantStrings` |

## What each proof contributes

All three proofs face one obstacle. Write a formula as a sum over assignments, and give each variable and clause a position in a grid or a word. The sum would split into small independent parts if no comparison of bits crossed between the parts. The comparisons do cross them.

### One Pigeonhole: a determinant removes the correction

In the parity approach, a comparison that flips all digits of a word is replaced by a low-degree polynomial in comparisons that flip few digits. The two differ by a low-rank matrix, and earlier routes pay for it: by enumerating measurements, or by a dynamic program on color counts.

This proof uses one identity. If all rows of `A - D` lie in a space of dimension at most `r`, then

```text
det D = Σ_{|T| ≤ r} (-1)^|T| det⟨T⟩,
```

where `⟨T⟩` takes the rows in `T` from `A - D` and the other rows from `A`. The expansion stops at `r` because a determinant with more than `r` rows in that space is `0`.

- **No factorization of the correction.** A permanent has the analogous expansion but not this vanishing, so the proof needs a determinant. The algorithm enumerates no value on the eigenvectors where the polynomial fails.
- **One pigeonhole.** The expansion has low total degree, so some digit has a low exponent. This replaces Hermite recovery. There is no recursion beyond sparsification.
- **One explicit formula.** The algorithm evaluates a single formula. On formulas with few occurrences per variable, the formula counts the solutions.
- **Limits.** The paper proves that no expansion of this kind can keep all its comparisons within fewer than `Q/2` of the `Q` digits, and it bounds the number of products.

The expansion itself is one line from multilinearity. Its use here is what is new: we did not find it used this way in the cited works or in web searches.

### Uncrossing Wires: a potential closes the recursion

View a formula as a network: nodes on a grid, joined by wires that each hold a bit. Two wires across a rectangle can be replaced by two terms, one crossing only the rows and one crossing only the columns. The difficulty is measuring progress: the number of wires need not fall, because a rectangle with wires on only one diagonal keeps all of them.

Those wires then occupy fewer pairs of nodes, and a quadratic potential sees this. For every term, in one of the two directions, the potential falls by the fixed factor `√(24/25)`, whatever the weights are.

- **Elementary.** Besides the branching that reduces occurrences, the proof uses one identity on four bits, a count of strings, and the Cauchy–Schwarz inequality. It has no polynomial approximation, no spectral argument, and no determinant.
- **Arbitrary weights.** Weights need not be balanced, so no node is regrouped.
- **One recursion.** The recursion runs on one fixed tower of grids, with two pieces for each rectangle.

The closest earlier proof is Claude's, which supplies the grid, the rectangles and the choice of merging rows or columns. The potential takes the place of its regrouping step.

### Dominant Strings: difference marks on the same recursion

This paper proves the part before sparsification: for each `Δ` and `ε`, the solutions of a 3-CNF in which every variable occurs at most `Δ` times are counted in time `C n^c 2^{εn}`. Each wire is marked by the difference of the bits at its two ends, so two crossing wires satisfy `X = V − H`: a vertical pair minus a horizontal pair. For `t` pairs on one rectangle, the `2^t` strings over `{V, H}` split by majority, with ties broken by the last letter. The strings with more `H` are summed across the rows and the others across the columns, and equal product terms coincide. Each half then needs at most `t − 1 + ⌈8⌊t/2⌋/5⌉ < 1.8t` wires in place of `2t`: `t − 1` bits name the string, and one base-3 number names its letters. The quadratic potential falls by `√0.91` per level.

The paper was written to be presented in an explanatory video and to a general audience, so its steps are elementary and can be drawn, and it uses plain names for standard objects. Its introduction gives the tensor-network names: the mark of a wire is the 2×2 Levi-Civita matrix, and `X = V − H` is the Schouten identity.

- **One theorem without branching.** The Lean end theorem `machine_bounded` covers formulas with few occurrences and does not use the branching tree; the sparsification lemma then gives the general case.

**Relation to Uncrossing Wires.** The two papers can be read independently, and they share one recursion: the tower of grids, two pieces per rectangle grouped by majority, and the quadratic potential, which Uncrossing Wires introduced. Dominant Strings changes three things. Its wires carry differences of bits instead of equality tests, so all three terms of `X = V − H` are products of differences; in Uncrossing Wires the identity `[x=v][y=u] = U − S` mixes equality tests and differences. A tie is broken by the last letter, so every rectangle uses all its pairs instead of an odd number of them, and the potential falls by `√0.91` instead of `√(24/25)` per level. Its theorem counts solutions of formulas with few occurrences, without branching, while Uncrossing Wires proves the 3-SAT theorem with the branching inside its proof.

### Side by side

| | One Pigeonhole | Uncrossing Wires | Dominant Strings |
|---|---|---|---|
| Handles the crossing wires by | truncated expansion of a determinant | one-bit identity, recursion with a potential | `X = V − H` with difference marks, the same recursion |
| Recovers the value by | pigeonhole on exponents | sum over chains | sum over chains |
| Main finding | the correction need not be factored | a measure that falls at every level | one kind of mark at every level, and all pairs of a rectangle used |
| Closest earlier route | O'Donnell | Claude | Uncrossing Wires, then Claude |

Each paper has a fuller comparison with the works of OpenAI, Claude, O'Donnell and Kintali, and it states what it takes from them.

## Formalization

Each proof is a Lean 4 library that ends in the theorem `Machine.not_ETH`, and all three reach the same statements in [`lean/TransposeBase/Statements.lean`](lean/TransposeBase/Statements.lean):

- **Word program.** One program for each `ε` decides 3-SAT, with at most `C (n+1)^b 2^{εn}` word operations.
- **Multitape machine.** One primitive multitape machine for each `ε` decides 3-SAT on a fixed encoding, in at most `C (ℓ+1)^d 2^{εn}` steps, where `ℓ` is the length of the encoding. Every prefix of the run visits at most `C' (ℓ+1)^{d'}` tape cells. The machine model is that of [OpenAI's Lean development](lean/third_party/openai-machine), included with its license.

`DominantStrings` also proves the statements of [`lean/DominantStrings/Statements.lean`](lean/DominantStrings/Statements.lean) for formulas with at most `D` occurrences of each variable, with the same time and space and without the branching tree.

The audit files report that the end theorems depend only on `propext`, `Classical.choice` and `Quot.sound`, and the libraries contain no `sorry`. We also replayed our own libraries with `lean4checker`; Mathlib and the third-party code were not replayed. To build and check, see [`lean/README.md`](lean/README.md).

The end theorem has the form that refuting ETH requires: for each `ε`, a machine. Its parameters and the width of the words are explicit in the proof. One algorithm with running time `2^{o(n)}` is a stronger statement, which Lean does not state.

The program of `OnePigeonhole` holds its small determinants in a very large literal table, in place of determinant code; the mathematics does not need the table. The Lean proofs differ from the text in some details, and a section of each paper lists the differences.

## Context

The organizers of the community examination of the OpenAI claim, Impagliazzo, Paturi and Williams, [call](https://ethdiscussion.blog/2026/10/26/eth-refutation-examination-and-discussion/) for "an understanding that others can reconstruct, question, and build upon". They also ask how simplified proofs and shared resources can make the argument accessible. This work is not part of that effort, but it shares these goals: the first two proofs come with a short version to reconstruct, each proof comes with scripts that test its identities, and a map from the text to the Lean statements.

The argument and the Lean proofs were developed in interactive sessions with Claude (Anthropic), building on the public manuscripts cited in the papers. The papers are preprints and have not been peer-reviewed.

## Layout

- `papers/<name>/`: one directory per paper, with `main.tex`, `paper.pdf`, a `README.md`, and, for some, scripts in `checks/`.
- `lean/`: one Lean project shared by all papers. Each paper has a library in it. See [`lean/README.md`](lean/README.md).

To add a paper: create `papers/<name>/`, add its library to `lean/lakefile.toml`, add its audit file, and add a row above.
Paths inside a paper are relative to its directory, except `lean/`, which is relative to the root of this repository.
