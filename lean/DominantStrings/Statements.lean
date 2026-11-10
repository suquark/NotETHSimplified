import TransposeBase.Statements
import SatBase.SparsificationRules

/-!
# The statements for formulas with few occurrences

The paper of this library proves its algorithm for 3-CNF formulas in which every variable occurs in at most `D`
clauses, for a fixed `D`. These are the end statements of that case, at the pseudocode layer and on the primitive
machine. `Audit.lean` checks by `rfl` that the end theorems are these.
-/

namespace DominantStrings

open SatBase TransposeBase TransposeBase.Pseudo TransposeBase.Pseudo.CnfTree

/-- `PseudoWide` for the formulas in which every variable occurs in at most `D` clauses. The occurrences of a variable
`v` are counted by `variableOccurrences F v`: the number of clauses that contain the literal `v`, plus the number of
clauses that contain the literal `¬v`. -/
def PseudoBounded (D : ℕ) (ε : ℝ) : Prop :=
  ∃ (P : Expr) (C : ℝ) (b c : ℕ), 8 ≤ c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3),
    (∀ v, variableOccurrences F v ≤ D) → ∀ (W : ℕ) (rest : List ℕ), c * (n + 1) ^ 3 ≤ W →
    let env := encF n F :: n :: rest
    (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
    (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n)

namespace Machine

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- The occurrences of the variable `v` in `G`: the number of clauses that contain the literal `v`, plus the number of
clauses that contain the literal `¬v`. -/
def occurrences {n : ℕ} (G : SAT.CNF (Fin n)) (v : Fin n) : ℕ :=
  (G.filter (fun C => (⟨v, false⟩ : SAT.Literal (Fin n)) ∈ C)).card +
    (G.filter (fun C => (⟨v, true⟩ : SAT.Literal (Fin n)) ∈ C)).card

/-- `RunsWithin`, for the inputs in which every variable occurs in at most `D` clauses. The statements are about one run
of `machine` from `encodeCNF G`: the run ends with `answer`, `answer` is correct, the number of steps is below the
runtime bound, and on every prefix the visited space is at most `C' * (ℓ + 1) ^ d'`. -/
def RunsWithinBounded (machine : PrimitiveMachine) (width D : ℕ) (C : ℝ) (d : ℕ) (ε : ℝ) (C' d' : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SAT.CNF (Fin n)), SAT.WidthAtMost width G → (∀ v, occurrences G v ≤ D) →
    ∃ (answer : Bool) (time : ℕ) (e : LocatedCfg machine),
      Computation.Trace (locatedStep machine) time (locatedInit machine (Encoding.encodeCNF G)) e ∧
      e.config.state = .inl answer ∧
      (answer = true ↔ SAT.Satisfiable G) ∧
      (time : ℝ) ≤ runtimeBound C d ε (Encoding.formulaBitLength G) n ∧
      ∀ (k : ℕ) (x : LocatedCfg machine), k ≤ time →
        Computation.Trace (locatedStep machine) k (locatedInit machine (Encoding.encodeCNF G)) x →
        visitedSpace x ≤ C' * (Encoding.formulaBitLength G + 1) ^ d'

/-- For every bound `D` and every `ε > 0` there is one primitive machine that decides 3-SAT on the fixed encoding, for
the inputs in which every variable occurs in at most `D` clauses, with this time and space. -/
def MachineBounded (D : ℕ) (ε : ℝ) : Prop :=
  ∃ (machine : PrimitiveMachine) (C : ℝ) (d C' d' : ℕ), 0 < C ∧ 0 < d ∧ RunsWithinBounded machine 3 D C d ε C' d'

end Machine

end DominantStrings
