import TransposeBase.Pseudo.Cnf
import TransposeBase.Pseudo.TreeWalk
import TransposeBase.Sat

/-!
# States on path words, and the link between `Reach` and the traversal

`stateW hL s0 w` is the state at the path word `w`, computed from the root state `s0` along the bits of `w`.
This file is the specification. It connects `sparseTree`, the preorder of `TreeWalk` and `Reach`.
-/

namespace TransposeBase.Pseudo.CnfTree

open SatBase Finset TransposeBase.Sat

variable {n L : ℕ}

theorem rule_leaf_iff {F : ClauseSet (SignedLiteral n)} :
    ruleCap n ≤ firstElig F L (ruleCap n) ↔ chooseSparseRule F L = none := by
  constructor
  · intro hle
    cases hs : chooseSparseRule F L with
    | none => rfl
    | some r =>
      have := (chooseSparseRule_some hs).1
      omega
  · intro h
    rw [chooseSparseRule_none.mp h]

/-- The state at a path word. The words `0` and `1` name the root. -/
noncomputable def stateW (hL : 2 ≤ L) (s0 : SparseState n L) (w : ℕ) : SparseState n L :=
  if h : w ≤ 1 then s0 else stepS hL (stateW hL s0 (w / 2)) (decide (w % 2 = 1))
decreasing_by omega

theorem stateW_le_one (hL : 2 ≤ L) (s0 : SparseState n L) {w : ℕ} (h : w ≤ 1) :
    stateW hL s0 w = s0 := by
  rw [stateW, dif_pos h]

theorem stateW_step (hL : 2 ≤ L) (s0 : SparseState n L) {w : ℕ} (h : 2 ≤ w) :
    stateW hL s0 w = stepS hL (stateW hL s0 (w / 2)) (decide (w % 2 = 1)) := by
  rw [stateW, dif_neg (by omega)]

theorem stateW_left (hL : 2 ≤ L) (s0 : SparseState n L) {w : ℕ} (h : 1 ≤ w) :
    stateW hL s0 (2 * w) = stepS hL (stateW hL s0 w) false := by
  rw [stateW_step hL s0 (by omega), show 2 * w / 2 = w by omega]
  congr 1
  simp

theorem stateW_right (hL : 2 ≤ L) (s0 : SparseState n L) {w : ℕ} (h : 1 ≤ w) :
    stateW hL s0 (2 * w + 1) = stepS hL (stateW hL s0 w) true := by
  rw [stateW_step hL s0 (by omega), show (2 * w + 1) / 2 = w by omega]
  congr 1
  simp

/-- The node at the word `p` is internal: its state has a rule. -/
def IntAt (hL : 2 ≤ L) (s0 : SparseState n L) (p : ℕ) : Prop :=
  chooseSparseRule (stateW hL s0 p).formula L ≠ none

noncomputable instance (hL : 2 ≤ L) (s0 : SparseState n L) : DecidablePred (IntAt hL s0) :=
  Classical.decPred _

theorem agrees_sparseTree (hL : 2 ≤ L) (s0 s : SparseState n L) :
    ∀ w, 1 ≤ w → stateW hL s0 w = s → Agrees (IntAt hL s0) (sparseTree hL s) w := by
  revert s
  apply sparseTree.induct hL
    (fun s => ∀ w, 1 ≤ w → stateW hL s0 w = s → Agrees (IntAt hL s0) (sparseTree hL s) w)
  · intro t ht w _ hw
    rw [sparseTree_none hL t ht]
    simp only [Agrees, IntAt, hw, ne_eq, not_not]
    exact ht
  · intro t r hr ihl ihr w hw1 hw
    rw [sparseTree_some hL t r hr]
    refine ⟨?_, ihl (2 * w) (by omega) ?_, ihr (2 * w + 1) (by omega) ?_⟩
    · simp only [IntAt, hw, hr, ne_eq, reduceCtorEq, not_false_eq_true]
    · rw [stateW_left hL s0 hw1, hw, stepS_some hL t false r hr]
      rfl
    · rw [stateW_right hL s0 hw1, hw, stepS_some hL t true r hr]
      rfl

theorem reach_of_mem (hL : 2 ≤ L) (s0 s : SparseState n L) :
    ∀ w, 1 ≤ w → stateW hL s0 w = s → ∀ p ∈ pre (sparseTree hL s) w, ¬ IntAt hL s0 p →
      Reach hL s (stateW hL s0 p) := by
  revert s
  apply sparseTree.induct hL
    (fun s => ∀ w, 1 ≤ w → stateW hL s0 w = s → ∀ p ∈ pre (sparseTree hL s) w, ¬ IntAt hL s0 p →
      Reach hL s (stateW hL s0 p))
  · intro t ht w _ hw p hp _
    rw [sparseTree_none hL t ht] at hp
    simp only [pre, List.mem_singleton] at hp
    subst hp
    rw [hw]
    exact Reach.leaf t ht
  · intro t r hr ihl ihr w hw1 hw p hp hi
    rw [sparseTree_some hL t r hr] at hp
    simp only [pre, List.mem_cons, List.mem_append] at hp
    rcases hp with rfl | hp | hp
    · exfalso
      apply hi
      simp only [IntAt, hw, hr, ne_eq, reduceCtorEq, not_false_eq_true]
    · refine Reach.left t r hr _ (ihl (2 * w) (by omega) ?_ p hp hi)
      rw [stateW_left hL s0 hw1, hw, stepS_some hL t false r hr]
      rfl
    · refine Reach.right t r hr _ (ihr (2 * w + 1) (by omega) ?_ p hp hi)
      rw [stateW_right hL s0 hw1, hw, stepS_some hL t true r hr]
      rfl

theorem mem_of_reach (hL : 2 ≤ L) (s0 : SparseState n L) {s t : SparseState n L} (h : Reach hL s t) :
    ∀ w, 1 ≤ w → stateW hL s0 w = s →
      ∃ p ∈ pre (sparseTree hL s) w, stateW hL s0 p = t ∧ ¬ IntAt hL s0 p := by
  induction h with
  | leaf s hs =>
    intro w _ hw
    rw [sparseTree_none hL s hs]
    refine ⟨w, by simp [pre], hw, ?_⟩
    simp only [IntAt, hw, ne_eq, not_not]
    exact hs
  | left s r hr t _ ih =>
    intro w hw1 hw
    obtain ⟨p, hp, h1, h2⟩ := ih (2 * w) (by omega) (by
      rw [stateW_left hL s0 hw1, hw, stepS_some hL s false r hr]
      rfl)
    rw [sparseTree_some hL s r hr]
    exact ⟨p, by simp [pre, hp], h1, h2⟩
  | right s r hr t _ ih =>
    intro w hw1 hw
    obtain ⟨p, hp, h1, h2⟩ := ih (2 * w + 1) (by omega) (by
      rw [stateW_right hL s0 hw1, hw, stepS_some hL s true r hr]
      rfl)
    rw [sparseTree_some hL s r hr]
    exact ⟨p, by simp [pre, hp], h1, h2⟩

/-- A word of the tree of `s0` fits in `10 * n * L + 1` bits. -/
theorem word_bound (hL : 2 ≤ L) (s0 : SparseState n L) {p : ℕ} (hp : p ∈ pre (sparseTree hL s0) 1) :
    p + 1 ≤ 2 ^ (10 * n * L + 1) := by
  have h1 := lt_of_mem_pre hp
  have h2 := sparseTree_height hL s0
  calc p + 1 ≤ (1 + 1) * 2 ^ (sparseTree hL s0).height := h1
    _ = 2 ^ ((sparseTree hL s0).height + 1) := by ring
    _ ≤ 2 ^ (10 * n * L + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

end TransposeBase.Pseudo.CnfTree
