import TransposeBase.Pseudo.CnfCode
import TransposeBase.Machine.FinalRun

/-!
# The end statements

The statements that every proof in this project reaches. Each library's `Audit.lean` checks by `rfl` that its end theorems are these.
-/

namespace TransposeBase

open SatBase TransposeBase.Pseudo TransposeBase.Pseudo.CnfTree

/-- For every `ε > 0` the program `P` comes before `n` and `F`, so it does not depend on the input. -/
def PseudoMain (ε : ℝ) : Prop :=
  ∃ (P : Expr) (C : ℝ) (b c : ℕ), 0 < c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3),
    let W := c * (n + 1) ^ 3
    let env := [encF n F, n]
    (encF n F < 2 ^ W ∧ n < 2 ^ W) ∧
    (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
    (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n)

/-- `PseudoMain` for every word size `W ≥ c * (n + 1) ^ 3` and every environment below `encF n F :: n`. -/
def PseudoWide (ε : ℝ) : Prop :=
  ∃ (P : Expr) (C : ℝ) (b c : ℕ), 8 ≤ c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3)
    (W : ℕ) (rest : List ℕ), c * (n + 1) ^ 3 ≤ W →
    let env := encF n F :: n :: rest
    (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
    (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n)

namespace Machine

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- All statements are about one run of `machine` from `encodeCNF G`, located on its tapes: the run ends with `answer`,
`answer` is correct, the number of steps is below the runtime bound, and on every prefix the visited space is at most
`C' * (ℓ + 1) ^ d'`. -/
def RunsWithin (machine : PrimitiveMachine) (width : ℕ) (C : ℝ) (d : ℕ) (ε : ℝ) (C' d' : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SAT.CNF (Fin n)), SAT.WidthAtMost width G →
    ∃ (answer : Bool) (time : ℕ) (e : LocatedCfg machine),
      Computation.Trace (locatedStep machine) time (locatedInit machine (Encoding.encodeCNF G)) e ∧
      e.config.state = .inl answer ∧
      (answer = true ↔ SAT.Satisfiable G) ∧
      (time : ℝ) ≤ runtimeBound C d ε (Encoding.formulaBitLength G) n ∧
      ∀ (k : ℕ) (x : LocatedCfg machine), k ≤ time →
        Computation.Trace (locatedStep machine) k (locatedInit machine (Encoding.encodeCNF G)) x →
        visitedSpace x ≤ C' * (Encoding.formulaBitLength G + 1) ^ d'

/-- For every `ε > 0` there is one primitive machine that decides 3-SAT on the fixed encoding, with this time and space. -/
def MachineMain (ε : ℝ) : Prop :=
  ∃ (machine : PrimitiveMachine) (C : ℝ) (d C' d' : ℕ), 0 < C ∧ 0 < d ∧
    DecidesWithBound machine 3 C d ε ∧ RunsWithin machine 3 C d ε C' d'

/-- For every exponent, 3-SAT on the fixed encoding is feasible on a primitive machine. -/
def EthFalse : Prop := ∀ ε > 0, ExponentFeasible 3 ε

/-- The **Exponential Time Hypothesis** for 3-SAT, in the machine model of this formalization: there is an exponent
`δ > 0` such that no primitive multitape machine decides 3-SAT, on the fixed encoding `encodeCNF`, within
`C * (ℓ + 1) ^ d * 2 ^ (δ * n)` steps for constants `C` and `d`, where `ℓ` is the length of the encoding and `n` is the
number of variables. -/
def ETH : Prop := ∃ δ > (0 : ℝ), ¬ ExponentFeasible 3 δ

end Machine

end TransposeBase
