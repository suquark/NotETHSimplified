import Mathlib.Data.Tree.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Depth-first preorder on binary trees, on path words

This file is pure Lean: it is the specification of the traversal, not a program.

A node is named by a word: the root has a word `s ≥ 1`, and the children of the node `p` are `2 * p` (left)
and `2 * p + 1` (right). For the root `s = 1` the leading bit is the length marker. The word `0` is the
sentinel.

`succWord int p` is the successor in preorder. It reads only the predicate `int` ("the node is internal"):

* an internal node goes to its left child `2 * p`;
* a leaf `p` goes to the odd part of `p + 1`. Adding one clears the trailing right moves and flips the last
  left move, and the odd part drops the cleared moves. If the odd part is `1`, there is no left move and
  the result is the sentinel.

`pre T s` lists the nodes of `T` in preorder. `walk_getElem` says that the iterates of `succWord` are exactly
this list and then the sentinel.
-/

namespace TransposeBase.Pseudo.CnfTree

open BinaryTree

/-- The odd part of a positive number. -/
def oddPart (q : ℕ) : ℕ :=
  if h : q = 0 then 0 else if q % 2 = 0 then oddPart (q / 2) else q
decreasing_by omega

theorem oddPart_two_mul {x : ℕ} (hx : 0 < x) : oddPart (2 * x) = oddPart x := by
  rw [oddPart, dif_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem oddPart_odd (x : ℕ) : oddPart (2 * x + 1) = 2 * x + 1 := by
  rw [oddPart, dif_neg (by omega), if_neg (by omega)]

/-- One step of the program that strips a trailing zero. -/
def stripStep (q : ℕ) : ℕ := if q % 2 ≤ 0 then q / 2 else q

/-- `m` steps of `stripStep` reach the odd part of a positive `q < 2 ^ m`. -/
theorem strip_iterate {m q : ℕ} (hq : 0 < q) (hm : q < 2 ^ m) : stripStep^[m] q = oddPart q := by
  induction m generalizing q with
  | zero => simp at hm; omega
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    by_cases h : q % 2 = 0
    · have h1 : stripStep q = q / 2 := by simp [stripStep, h]
      rw [h1, ih (by omega) (by rw [pow_succ] at hm; omega)]
      obtain ⟨x, rfl⟩ : ∃ x, q = 2 * x := ⟨q / 2, by omega⟩
      rw [oddPart_two_mul (by omega)]
      congr 1
      omega
    · have h1 : stripStep q = q := by simp [stripStep]; omega
      obtain ⟨x, rfl⟩ : ∃ x, q = 2 * x + 1 := ⟨q / 2, by omega⟩
      have h2 : ∀ k, stripStep^[k] (2 * x + 1) = 2 * x + 1 := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply']; rw [ih]; exact h1
      rw [h1, h2, oddPart_odd]

/-- The successor of a leaf. -/
def leafNext (p : ℕ) : ℕ :=
  if oddPart (p + 1) = 1 then 0 else oddPart (p + 1)

/-- The successor in preorder. -/
def succWord (int : ℕ → Prop) [DecidablePred int] (p : ℕ) : ℕ :=
  if p = 0 then 0 else if int p then 2 * p else leafNext p

/-- The nodes of `T` in preorder, when the root has the word `s`. -/
def pre : BinaryTree Unit → ℕ → List ℕ
  | .nil, s => [s]
  | .node _ l r, s => s :: (pre l (2 * s) ++ pre r (2 * s + 1))

/-- The predicate `int` describes the shape of `T` at the words of `T`. -/
def Agrees (int : ℕ → Prop) : BinaryTree Unit → ℕ → Prop
  | .nil, s => ¬ int s
  | .node _ l r, s => int s ∧ Agrees int l (2 * s) ∧ Agrees int r (2 * s + 1)

theorem length_pre (T : BinaryTree Unit) (s : ℕ) :
    (pre T s).length = T.numNodes + T.numLeaves := by
  induction T generalizing s with
  | nil => simp [pre, numNodes, numLeaves]
  | node _ l r ihl ihr =>
    simp only [pre, List.length_cons, List.length_append, ihl, ihr, numNodes, numLeaves]
    omega

/-- A full binary tree has fewer than twice as many nodes as leaves. -/
theorem length_pre_le (T : BinaryTree Unit) (s : ℕ) : (pre T s).length ≤ 2 * T.numLeaves := by
  have := T.numLeaves_eq_numNodes_succ
  rw [length_pre]
  omega

theorem pos_of_mem_pre {T : BinaryTree Unit} {s p : ℕ} (hs : 0 < s) (h : p ∈ pre T s) : 0 < p := by
  induction T generalizing s with
  | nil => simp [pre] at h; omega
  | node _ l r ihl ihr =>
    simp only [pre, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact hs
    · exact ihl (by omega) h
    · exact ihr (by omega) h

/-- The size of a word of `T`: this bounds the words that a traversal touches. -/
theorem lt_of_mem_pre {T : BinaryTree Unit} {s p : ℕ} (h : p ∈ pre T s) :
    p + 1 ≤ (s + 1) * 2 ^ T.height := by
  induction T generalizing s with
  | nil => simp [pre] at h; simp [h, height]
  | node _ l r ihl ihr =>
    simp only [pre, List.mem_cons, List.mem_append] at h
    simp only [height]
    set M := l.height ⊔ r.height with hM
    have hb : (s + 1) * 2 ^ (M + 1) = (2 * s + 2) * 2 ^ M := by ring
    rw [hb]
    have h1 : 2 ^ l.height ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) le_sup_left
    have h2 : 2 ^ r.height ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) le_sup_right
    rcases h with rfl | h | h
    · have : 1 ≤ 2 ^ M := Nat.one_le_two_pow
      nlinarith
    · have h3 := ihl h
      have h4 : (2 * s + 1) * 2 ^ l.height ≤ (2 * s + 2) * 2 ^ M :=
        Nat.mul_le_mul (by omega) h1
      exact h3.trans h4
    · have h3 := ihr h
      have h4 : (2 * s + 1 + 1) * 2 ^ r.height ≤ (2 * s + 2) * 2 ^ M :=
        Nat.mul_le_mul (by omega) h2
      exact h3.trans h4

/-- `p` lies below `s`. -/
def Below (s p : ℕ) : Prop := ∃ m, p / 2 ^ m = s

theorem below_of_mem_pre {T : BinaryTree Unit} {s p : ℕ} (h : p ∈ pre T s) : Below s p := by
  induction T generalizing s with
  | nil => simp [pre] at h; exact ⟨0, by simp [h]⟩
  | node _ l r ihl ihr =>
    simp only [pre, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact ⟨0, by simp⟩
    · obtain ⟨m, hm⟩ := ihl h
      refine ⟨m + 1, ?_⟩
      rw [pow_succ, ← Nat.div_div_eq_div_mul, hm]
      omega
    · obtain ⟨m, hm⟩ := ihr h
      refine ⟨m + 1, ?_⟩
      rw [pow_succ, ← Nat.div_div_eq_div_mul, hm]
      omega

/-- Two different children of a node have no common word below them. -/
theorem below_disjoint {s p : ℕ} (hs : 0 < s) (h1 : Below (2 * s) p) (h2 : Below (2 * s + 1) p) :
    False := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have : p / 2 ^ (a + c + 1) = p / 2 ^ a / 2 ^ (c + 1) := by
      rw [show a + c + 1 = a + (c + 1) by ring, pow_add, Nat.div_div_eq_div_mul]
    rw [this, ha] at hb
    have h3 : 2 * s / 2 ^ (c + 1) ≤ s := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_right_comm]
      have : 2 * s / 2 = s := by omega
      rw [this]
      exact Nat.div_le_self _ _
    omega
  · subst hab; omega
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have : p / 2 ^ (b + c + 1) = p / 2 ^ b / 2 ^ (c + 1) := by
      rw [show b + c + 1 = b + (c + 1) by ring, pow_add, Nat.div_div_eq_div_mul]
    rw [this, hb] at ha
    have h3 : (2 * s + 1) / 2 ^ (c + 1) ≤ s := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_right_comm]
      have : (2 * s + 1) / 2 = s := by omega
      rw [this]
      exact Nat.div_le_self _ _
    omega

/-- Every word appears once. -/
theorem nodup_pre (T : BinaryTree Unit) {s : ℕ} (hs : 0 < s) : (pre T s).Nodup := by
  induction T generalizing s with
  | nil => simp [pre]
  | node _ l r ihl ihr =>
    simp only [pre, List.nodup_cons, List.mem_append, not_or]
    refine ⟨⟨?_, ?_⟩, List.Nodup.append (ihl (by omega)) (ihr (by omega)) ?_⟩
    · intro h
      obtain ⟨m, hm⟩ := below_of_mem_pre h
      have : s / 2 ^ m ≤ s := Nat.div_le_self _ _
      omega
    · intro h
      obtain ⟨m, hm⟩ := below_of_mem_pre h
      have : s / 2 ^ m ≤ s := Nat.div_le_self _ _
      omega
    · intro p h1 h2
      exact below_disjoint hs (below_of_mem_pre h1) (below_of_mem_pre h2)

section Walk

variable (int : ℕ → Prop) [DecidablePred int]

/-- Starting at the root of `T`, the iterates of `succWord` run through `pre T s`, and after the whole list
they stand at `leafNext s`. -/
theorem walk_aux (T : BinaryTree Unit) {s : ℕ} (hs : 0 < s) (hA : Agrees int T s) :
    (∀ k (h : k < (pre T s).length), (succWord int)^[k] s = (pre T s)[k]) ∧
      (succWord int)^[(pre T s).length] s = leafNext s := by
  induction T generalizing s with
  | nil =>
    constructor
    · intro k h
      simp only [pre, List.length_cons, List.length_nil] at h
      obtain rfl : k = 0 := by omega
      rfl
    · simp only [pre, List.length_cons, List.length_nil, zero_add, Function.iterate_one]
      simp only [Agrees] at hA
      simp [succWord, hA, show s ≠ 0 by omega]
  | node _ l r ihl ihr =>
    obtain ⟨hi, hl, hr⟩ := hA
    obtain ⟨il, el⟩ := ihl (s := 2 * s) (by omega) hl
    obtain ⟨ir, er⟩ := ihr (s := 2 * s + 1) (by omega) hr
    have hstep : succWord int s = 2 * s := by simp [succWord, hi, show s ≠ 0 by omega]
    have hln : leafNext (2 * s) = 2 * s + 1 := by
      unfold leafNext
      rw [oddPart_odd, if_neg (by omega)]
    have hrn : leafNext (2 * s + 1) = leafNext s := by
      unfold leafNext
      rw [show 2 * s + 1 + 1 = 2 * (s + 1) by ring, oddPart_two_mul (by omega)]
    have hmid : (succWord int)^[(pre l (2 * s)).length] (2 * s) = 2 * s + 1 := by rw [el, hln]
    constructor
    · intro k h
      simp only [pre] at h ⊢
      cases k with
      | zero => rfl
      | succ k =>
        rw [Function.iterate_succ_apply, hstep, List.getElem_cons_succ]
        simp only [List.length_cons, List.length_append] at h
        by_cases hk : k < (pre l (2 * s)).length
        · rw [List.getElem_append_left hk]
          exact il k hk
        · rw [List.getElem_append_right (by omega)]
          obtain ⟨c, rfl⟩ : ∃ c, k = c + (pre l (2 * s)).length := ⟨k - (pre l (2 * s)).length, by omega⟩
          rw [Function.iterate_add_apply, hmid, ir c (by omega)]
          simp
    · simp only [pre, List.length_cons, List.length_append]
      rw [show (pre l (2 * s)).length + (pre r (2 * s + 1)).length + 1 =
          (pre r (2 * s + 1)).length + ((pre l (2 * s)).length + 1) by omega,
        Function.iterate_add_apply, Function.iterate_succ_apply, hstep, hmid, er, hrn]

theorem succWord_zero : succWord int 0 = 0 := by simp [succWord]

theorem succWord_iter_zero (k : ℕ) : (succWord int)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, succWord_zero, ih]

theorem leafNext_one : leafNext 1 = 0 := by
  have : oddPart 2 = oddPart 1 := oddPart_two_mul (x := 1) (by omega)
  have h1 : oddPart 1 = 1 := oddPart_odd 0
  simp [leafNext, this, h1]

/-- **The preorder fact.** From the root word `1`, the iterates of the successor list every node of `T`, once
each, and after that they stay on the sentinel `0`. -/
theorem walk_getElem (T : BinaryTree Unit) (hA : Agrees int T 1) :
    (pre T 1).Nodup ∧
      (∀ k (h : k < (pre T 1).length), (succWord int)^[k] 1 = (pre T 1)[k]) ∧
      ∀ k, (pre T 1).length ≤ k → (succWord int)^[k] 1 = 0 := by
  obtain ⟨h1, h2⟩ := walk_aux int T (by omega) hA
  refine ⟨nodup_pre T (by omega), h1, ?_⟩
  intro k hk
  obtain ⟨c, rfl⟩ : ∃ c, k = c + (pre T 1).length := ⟨k - (pre T 1).length, by omega⟩
  rw [Function.iterate_add_apply, h2, leafNext_one, succWord_iter_zero]

/-- Every iterate is the sentinel or a node. -/
theorem walk_mem (T : BinaryTree Unit) (hA : Agrees int T 1) (k : ℕ) :
    (succWord int)^[k] 1 = 0 ∨ (succWord int)^[k] 1 ∈ pre T 1 := by
  obtain ⟨_, h1, h2⟩ := walk_getElem int T hA
  by_cases hk : k < (pre T 1).length
  · right
    rw [h1 k hk]
    exact List.getElem_mem hk
  · left
    exact h2 k (by omega)

/-- Every node is an iterate before the list ends. -/
theorem walk_visits (T : BinaryTree Unit) (hA : Agrees int T 1) {p : ℕ} (hp : p ∈ pre T 1) :
    ∃ k, k < (pre T 1).length ∧ (succWord int)^[k] 1 = p := by
  obtain ⟨_, h1, _⟩ := walk_getElem int T hA
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  exact ⟨k, hk, h1 k hk⟩

end Walk

end TransposeBase.Pseudo.CnfTree
