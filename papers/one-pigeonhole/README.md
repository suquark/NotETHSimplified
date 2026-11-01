# One Pigeonhole for 3-SAT: A Determinant That Removes the Correction

- `paper.pdf`, `main.tex`: the paper.
- `proof.pdf`, `proof.tex`: the proof alone. It cites the sparsification lemma.
- `checks/check_example.py`: exact check of the worked example (standard library only).
- `checks/check_wires.py`: exact test of the formula of the proof against brute force, on small networks.
- `checks/check_proof.py`, `checks/check_proof_parts.py`: exact tests of `proof.tex` against brute force: the final formula, and
  its steps and constants (standard library only).

The Lean proof is the library `OnePigeonhole` in [`../../lean`](../../lean). Section 9 of the paper states what is formalized
and what is not. The chain reaches a multitape machine for 3-SAT (`OnePigeonhole.Machine.machine_main`, `not_ETH`). The program holds its small
determinants in a literal table.

```bash
cd ../../lean && lake exe cache get && lake build OnePigeonhole TransposeBase && lake env lean OnePigeonhole/Audit.lean && lake env lean OnePigeonhole/ClosureCheck.lean
```

The paper builds on OpenAI, *The Exponential Time Hypothesis is false*; Claude
(Anthropic), *A 2^{o(n)} time algorithm for 3-SAT*; R. O'Donnell, *Some exposition of "The Exponential Time Hypothesis
Is False"*; and S. Kintali, *A simplified proof of ETH is false*. The 3-SAT theorem is due to the first two. Section 1.1 of the paper says what is simplified.
