# Uncrossing Wires for 3-SAT: A Potential That Closes the Recursion

- `paper.pdf`, `main.tex`: the paper.
- `proof.pdf`, `proof.tex`: the proof alone. It cites the sparsification lemma.
- `checks/check_step.py`: exact test of Sections 2 and 3 on tiny networks (standard library only).

The Lean proof is the library `UncrossingWires` in [`../../lean`](../../lean). Section 8 of the paper states what is formalized
and what is not. The chain reaches a multitape machine for 3-SAT (`UncrossingWires.Machine.machine_main`, `not_ETH`).

```bash
cd ../../lean && lake exe cache get && lake build UncrossingWires TransposeBase && lake env lean UncrossingWires/Audit.lean && lake env lean UncrossingWires/ClosureCheck.lean
```

The companion paper [Dominant Strings for 3-SAT](../dominant-strings) runs the same recursion with wires that carry differences of bits, and proves the case of few occurrences per variable without branching.

The paper builds on Claude (Anthropic), *A 2^{o(n)} time algorithm for 3-SAT*; OpenAI, *The
Exponential Time Hypothesis is false*; R. O'Donnell, *Some exposition of "The Exponential Time Hypothesis Is False"*; and S. Kintali, *A simplified proof of ETH is false*. The 3-SAT theorem
is due to the first two.
