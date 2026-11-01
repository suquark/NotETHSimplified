import SatBase.PackingPotential
import SatBase.ClauseNormalization
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Init.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Ring.Parity
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import SatBase.SparsificationRules
import Mathlib.Data.List.Lex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-! The search state records only the invariants already proved for the
actual construction. Its remaining potential gives an explicit decreasing
natural number for recursive termination. -/
namespace SatBase

structure SparseState (n L : ℕ) where
  formula : ClauseSet (SignedLiteral n)
  normalized : normalizeClauses formula=formula
  width : ∀ C∈formula,C.card≤3

namespace SparseState
variable {n L : ℕ}

def left (s : SparseState n L) (hL : 2≤L)
    (r : ℕ × Finset (SignedLiteral n)) (hr : chooseSparseRule s.formula L=some r) :
    SparseState n L where
  formula := normalizedCoreLeft s.formula r.1 r.2
  normalized := normalizeClauses_idempotent _
  width := (chosen_rule_children s.formula s.width L (by omega) r hr).1

def right (s : SparseState n L) (hL : 2≤L)
    (r : ℕ × Finset (SignedLiteral n)) (hr : chooseSparseRule s.formula L=some r) :
    SparseState n L where
  formula := normalizedCoreRight s.formula r.1 r.2
  normalized := normalizeClauses_idempotent _
  width := (chosen_rule_children s.formula s.width L (by omega) r hr).2.1

noncomputable def remaining (s : SparseState n L) : ℕ := 10*n*L-packingPotential s.formula L

theorem potential_gains (s : SparseState n L) (hL : 2≤L)
    (r : ℕ × Finset (SignedLiteral n)) (hr : chooseSparseRule s.formula L=some r) :
    packingPotential s.formula L+1≤packingPotential (s.left hL r hr).formula L ∧
    packingPotential s.formula L+L^2≤packingPotential (s.right hL r hr).formula L := by
  have hh : chooseSparseRule (normalizeClauses s.formula) L=some r := by
    simpa only [s.normalized] using hr
  simpa only [s.normalized,left,right] using chosen_packing_gains s.formula L hL r hh

theorem remaining_gains (s : SparseState n L) (hL : 2≤L)
    (r : ℕ × Finset (SignedLiteral n)) (hr : chooseSparseRule s.formula L=some r) :
    (s.left hL r hr).remaining+1≤s.remaining ∧
    (s.right hL r hr).remaining+L^2≤s.remaining := by
  have hg := s.potential_gains hL r hr
  have hl := packingPotential_bound (s.left hL r hr).formula L
  have hr' := packingPotential_bound (s.right hL r hr).formula L
  unfold remaining
  omega

/-- The weighted decrease also certifies termination of both recursive calls. -/
theorem remaining_decreases (s : SparseState n L) (hL : 2≤L)
    (r : ℕ × Finset (SignedLiteral n)) (hr : chooseSparseRule s.formula L=some r) :
    (s.left hL r hr).remaining<s.remaining ∧ (s.right hL r hr).remaining<s.remaining := by
  have hg := s.remaining_gains hL r hr
  have hq : 0<L^2 := pow_pos (by omega) 2
  constructor <;> omega

end SparseState

def initialSparseState {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (hw : ∀ C∈F,C.card≤3) (L : ℕ) (_hL : 2≤L) : SparseState n L where
  formula := normalizeClauses F
  normalized := normalizeClauses_idempotent _
  width := fun C hC => hw C (normalizeClauses_subset F hC)

end SatBase
