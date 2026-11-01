import Mathlib.Data.Tree.Basic
import SatBase.SparsePotential
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The actual finite search tree and its size bound. The tree is a
mathematical record of all branches, not a data structure stored by DFS. -/
namespace SatBase

def sparseTree {n L : ℕ} (hL : 2≤L) (s : SparseState n L) : BinaryTree Unit :=
  match hr : chooseSparseRule s.formula L with
  | none => .nil
  | some r => .node () (sparseTree hL (s.left hL r hr)) (sparseTree hL (s.right hL r hr))
termination_by s.remaining
decreasing_by
  · exact (s.remaining_decreases hL r hr).1
  · exact (s.remaining_decreases hL r hr).2

theorem sparseTree_none {n L : ℕ} (hL : 2≤L) (s : SparseState n L)
    (hstop : chooseSparseRule s.formula L=none) : sparseTree hL s=.nil := by
  rw [sparseTree.eq_def]
  split
  · rfl
  · rename_i r hr
    simp [hstop] at hr

theorem sparseTree_some {n L : ℕ} (hL : 2≤L) (s : SparseState n L)
    (r : ℕ × Finset (SignedLiteral n)) (hr : chooseSparseRule s.formula L=some r) :
    sparseTree hL s=.node () (sparseTree hL (s.left hL r hr))
      (sparseTree hL (s.right hL r hr)) := by
  rw [sparseTree.eq_def]
  split
  · rename_i hn
    simp [hr] at hn
  · rename_i r' hr'
    have he : r=r' := by simpa only [hr,Option.some.injEq] using hr'
    subst r'
    rfl

/-- Apply the same remaining-potential bound directly to leaf counts. -/
theorem sparseTree_leaves {n L : ℕ} (hL : 2≤L) (s : SparseState n L) :
    ((sparseTree hL s).numLeaves:ℝ)≤Real.exp ((20*Real.log L+10)*n/L) := by
  have h := sparsePotential_exp_bound hL (fun t => ((sparseTree hL t).numLeaves:ℝ)) 1
    (by norm_num) (fun t ht => by rw [sparseTree_none hL t ht]; simp)
    (fun t r hr => by rw [sparseTree_some hL t r hr]; simp [BinaryTree.numLeaves]) s
  simpa only [one_mul] using h

/-- Each recursive step decreases the same natural-valued measure, so it
also bounds ordinary path length. No weighted-height object is needed. -/
theorem sparseTree_height {n L : ℕ} (hL : 2≤L) (s : SparseState n L) :
    (sparseTree hL s).height≤10*n*L := by
  have hrec : ∀ t : SparseState n L,(sparseTree hL t).height≤t.remaining := by
    apply sparseTree.induct hL
    · intro t ht
      rw [sparseTree_none hL t ht]
      exact Nat.zero_le _
    · intro t r hr ihl ihr
      rw [sparseTree_some hL t r hr]
      simp only [BinaryTree.height]
      have hg := t.remaining_decreases hL r hr
      omega
  exact (hrec s).trans (Nat.sub_le _ _)

end SatBase
