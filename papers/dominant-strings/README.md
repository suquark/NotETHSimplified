# Dominant Strings for 3-SAT: Counting Solutions with Few Occurrences per Variable

- `paper.pdf`, `main.tex`: the paper.
- `proof.pdf`, `proof.tex`: the proof alone, of the counting theorem and of the corollary for 3-SAT. It cites the sparsification lemma.

The paper counts the solutions of a 3-CNF in which every variable occurs at most `Δ` times, in time
`C n^c 2^{εn}`. With the sparsification lemma of Impagliazzo, Paturi and Zane this refutes ETH.

The Lean proof is the library `DominantStrings` in [`../../lean`](../../lean). Section 8 of the paper states what is
formalized and what is not. The end theorems are `DominantStrings.Pseudo.Final.pseudo_bounded` and
`DominantStrings.Machine.machine_bounded`, for formulas with few occurrences, without branching; the library also joins
the same chain with the branching tree of `SatBase` into `DominantStrings.Machine.not_ETH`.

```bash
cd ../../lean && lake exe cache get && lake build DominantStrings TransposeBase && lake env lean DominantStrings/Audit.lean && lake env lean DominantStrings/ClosureCheck.lean
```

The paper is a companion of [Uncrossing Wires for 3-SAT](../uncrossing-wires) and reads independently of it. It uses the same recursion and potential, with wires that carry differences of bits, ties broken by the last letter so that every rectangle uses all its pairs, and a theorem for few occurrences without branching. The introduction states the relation in full. The paper was written to be presented in an explanatory video and to a general audience, so it uses plain names for standard objects; the introduction gives their tensor-network names.

The paper builds on Claude (Anthropic), *A 2^{o(n)} time algorithm for 3-SAT*; OpenAI, *The
Exponential Time Hypothesis is false*; R. O'Donnell, *Some exposition of "The Exponential Time Hypothesis Is False"*; and
S. Kintali, *A simplified proof of ETH is false*. The 3-SAT theorem is due to the first two.
