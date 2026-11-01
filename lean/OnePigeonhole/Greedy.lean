import TransposeBase.Pseudo.PlaceCore
import OnePigeonhole.Net

/-!
# The placement

The placement of Section 1 of `papers/one-pigeonhole/proof.tex`, on numbers. A network has the wires `e : Fin m` and the nodes
`Fin v`, with the shape `Shape`: the tail of each wire is a node below `n`, and the head of each wire is a node at least `n`. The words are
the numbers below `L ^ Q`, read by their digits in base `L`, and `L = 6 * Q`.

* A node `α < n` gets the word `α % L ^ Q`.
* The other nodes are placed in the order of their numbers. Let `R` be the table of the words of the nodes below `α`, one field for each
  node. `load x y` is the number of wires with head below `α`, tail word `x` and head word `y`, and `score y` is the sum of
  `load (word of tail e) y` over the wires `e` with head `α`.
* `clash` counts the digits where the word `y` has the letter of the word of a tail of `α`. So `clash = 0` exactly when `y` differs in every
  digit from these words. Among these words, the node `α` gets the word with the least `score`, the smallest such word on ties. `adj` is
  `score` on these words, and above all scores on the others.

`table α` is the table of the words of the nodes below `α`.

* `card_allowed`: at least half of the words are allowed. Each wire into `α` and each digit forbid `1 / L` of the words, and there are at
  most `3 * Q` such pairs. This is the bound `(L - 3) ^ Q ≥ K / 2` of the text, by a union over the forbidden letters.
* `score_best_le`: the minimum is at most the average over the allowed words.
* `load_table_le`: all loads stay at most `capB n K D = 6 * capA n K D / K + 3`, with `K = L ^ Q`.
* `sq_mul_capB_le`: `K ^ 2 * capB n K D ≤ 13 * D * n` for `K ^ 2 ≤ n` and `3 ≤ D`.
* `layN`: the layer of a wire, the number of earlier wires with the same tail word and head word.
* `wiresOf`, `onNodes_wiresOf`: the wires of `Wires.lean`, on the words of the nodes.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Greedy

open Finset TransposeBase.Pseudo.Code
open TransposeBase.Pseudo.Place (fld fld_add_low fld_add_self add_mul_lt)

variable {m v : ℕ}

/-- The shape of the network of a formula: tails below `n`, heads at least `n`, at most `D` wires with one tail, and at
most `3` wires with one head. -/
structure Shape (n D : ℕ) (tail head : Fin m → Fin v) : Prop where
  tail_lt : ∀ e, (tail e : ℕ) < n
  le_head : ∀ e, n ≤ (head e : ℕ)
  card_tail : ∀ a, #{e | tail e = a} ≤ D
  card_head : ∀ a, #{e | head e = a} ≤ 3

/-! ### The table -/

section Defs

variable (fw n Q L : ℕ) (tail head : Fin m → Fin v)

/-- The number of wires with head below `α`, tail word `x` and head word `y`, for the words in the table `R`. -/
def load (R α x y : ℕ) : ℕ :=
  ∑ e : Fin m, if (head e : ℕ) < α ∧ fld fw R (tail e) = x ∧ fld fw R (head e) = y then 1 else 0

/-- The sum of the loads from the words of the tails of the node `α` towards the word `y`. -/
def score (R α y : ℕ) : ℕ :=
  ∑ e : Fin m, if (head e : ℕ) = α then load fw tail head R α (fld fw R (tail e)) y else 0

/-- The number of pairs of a wire into `α` and a digit where the word `y` has the letter of the word of the tail. -/
def clash (R α y : ℕ) : ℕ :=
  ∑ e : Fin m, if (head e : ℕ) = α then
    ∑ i ∈ range Q, (if dig L (fld fw R (tail e)) i = dig L y i then 1 else 0) else 0

/-- The number that the node `α` minimizes: the score on the allowed words, and a number above all scores on the others. -/
def adj (R α y : ℕ) : ℕ :=
  if clash fw Q L tail head R α y ≤ 0 then score fw tail head R α y else m * m + 1

/-- The first word with the minimal `adj` among the words below `y`. -/
def best (R α : ℕ) : ℕ → ℕ
  | 0 => 0
  | y + 1 =>
    if adj fw Q L tail head R α (best R α y) ≤ adj fw Q L tail head R α y then best R α y else y

/-- The word of the node `α`, for the table `R` of the nodes below `α`. -/
def word (R α : ℕ) : ℕ := if n ≤ α then best fw Q L tail head R α (L ^ Q) else α % L ^ Q

/-- The table of the words of the nodes below `α`, with fields of width `fw`. -/
def table : ℕ → ℕ
  | 0 => 0
  | α + 1 => table α + word fw n Q L tail head (table α) α * 2 ^ (α * fw)

end Defs

/-- The number of wires with the tail on one word is at most this. -/
def capA (n K D : ℕ) : ℕ := (n / K + 1) * D

/-- All loads are at most this. -/
def capB (n K D : ℕ) : ℕ := 6 * capA n K D / K + 3

variable {fw n Q L D : ℕ} {tail head : Fin m → Fin v}

/-! ### Counting the wires -/

/-- At most `n / K + 1` numbers below `n` have one remainder. -/
theorem card_mod_le (K n x : ℕ) : #{u ∈ range n | u % K = x} ≤ n / K + 1 := by
  have h : #{u ∈ range n | u % K = x} ≤ #(range (n / K + 1)) := by
    refine card_le_card_of_injOn (fun u => u / K) (fun u hu => ?_) (fun u hu u' hu' h => ?_)
    · have h1 := (mem_filter.mp (mem_coe.mp hu)).1
      exact mem_coe.mpr (mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp h1).le)))
    · have h1 := (mem_filter.mp (mem_coe.mp hu)).2
      have h2 := (mem_filter.mp (mem_coe.mp hu')).2
      simp only at h
      rw [← Nat.div_add_mod u K, ← Nat.div_add_mod u' K, h, h1, h2]
  simpa using h

/-- The number of wires with the tail on one word. -/
theorem card_tail_word_le {K : ℕ} (S : Shape n D tail head) (x : ℕ) :
    #{e | (tail e : ℕ) % K = x} ≤ capA n K D := by
  have h1 := card_le_mul_card_image (s := ({e | (tail e : ℕ) % K = x} : Finset (Fin m)))
    (f := fun e => (tail e : ℕ)) D (fun a ha => by
      obtain ⟨e0, -, rfl⟩ := mem_image.mp ha
      refine (card_le_card fun e he => ?_).trans (S.card_tail (tail e0))
      exact mem_filter.mpr ⟨mem_univ _, Fin.ext (mem_filter.mp he).2⟩)
  have h2 : #(({e | (tail e : ℕ) % K = x} : Finset (Fin m)).image fun e => (tail e : ℕ)) ≤ n / K + 1 := by
    refine (card_le_card fun u hu => ?_).trans (card_mod_le K n x)
    obtain ⟨e, he, rfl⟩ := mem_image.mp hu
    exact mem_filter.mpr ⟨mem_range.mpr (S.tail_lt e), (mem_filter.mp he).2⟩
  calc _ ≤ _ := h1
    _ ≤ D * (n / K + 1) := Nat.mul_le_mul_left _ h2
    _ = capA n K D := by rw [capA, mul_comm]

theorem card_head_le (S : Shape n D tail head) (α : ℕ) : #{e | (head e : ℕ) = α} ≤ 3 := by
  by_cases hα : α < v
  · refine (card_le_card fun e he => ?_).trans (S.card_head ⟨α, hα⟩)
    exact mem_filter.mpr ⟨mem_univ _, Fin.ext (mem_filter.mp he).2⟩
  · have : ({e | (head e : ℕ) = α} : Finset (Fin m)) = ∅ := by
      refine filter_eq_empty_iff.mpr fun e _ h => hα ?_
      rw [← h]
      exact (head e).2
    rw [this]
    simp

/-! ### The sums of the loads and of the scores -/

/-- The loads from one word add up to at most the number of wires with the tail on this word. -/
theorem sum_load_le {K : ℕ} (S : Shape n D tail head) {R α : ℕ} (hR : ∀ u < n, fld fw R u = u % K) (x : ℕ) :
    ∑ y ∈ range K, load fw tail head R α x y ≤ capA n K D := by
  unfold load
  rw [sum_comm]
  refine le_trans ?_ (card_tail_word_le S x)
  rw [card_filter]
  refine sum_le_sum fun e _ => ?_
  rw [← hR _ (S.tail_lt e)]
  by_cases hx : fld fw R (tail e) = x
  · rw [if_pos hx]
    calc ∑ y ∈ range K, (if (head e : ℕ) < α ∧ fld fw R (tail e) = x ∧ fld fw R (head e) = y then 1 else 0)
        ≤ ∑ y ∈ range K, (if fld fw R (head e) = y then 1 else 0) :=
          sum_le_sum fun y _ => by
            by_cases h : fld fw R (head e) = y
            · rw [if_pos h]
              split_ifs <;> omega
            · rw [if_neg h, if_neg (fun hh => h hh.2.2)]
      _ ≤ 1 := by
          rw [sum_ite_eq]
          split_ifs <;> omega
  · rw [if_neg hx]
    exact le_of_eq (sum_eq_zero fun y _ => if_neg fun hh => hx hh.2.1)

/-- The scores add up to at most three times the bound on the loads from one word. -/
theorem sum_score_le {K : ℕ} (S : Shape n D tail head) {R α : ℕ} (hR : ∀ u < n, fld fw R u = u % K) :
    ∑ y ∈ range K, score fw tail head R α y ≤ 3 * capA n K D := by
  unfold score
  rw [sum_comm]
  calc ∑ e : Fin m, ∑ y ∈ range K, (if (head e : ℕ) = α then load fw tail head R α (fld fw R (tail e)) y else 0)
      ≤ ∑ e : Fin m, (if (head e : ℕ) = α then capA n K D else 0) :=
        sum_le_sum fun e _ => by
          split_ifs
          · exact sum_load_le S hR _
          · simp
    _ = #{e | (head e : ℕ) = α} * capA n K D := by
        rw [← sum_filter, sum_const, smul_eq_mul]
    _ ≤ 3 * capA n K D := Nat.mul_le_mul_right _ (card_head_le S α)

/-- No wire has a head below `n`. -/
theorem load_eq_zero (S : Shape n D tail head) {α : ℕ} (hα : α ≤ n) (R x y : ℕ) : load fw tail head R α x y = 0 :=
  sum_eq_zero fun e _ => if_neg fun h => by
    have := S.le_head e
    omega

/-- One step of the placement adds the wires with head `α`. -/
theorem load_step (S : Shape n D tail head) {R α w : ℕ} (hα : n ≤ α) (hR : R < 2 ^ (α * fw)) (hw : w < 2 ^ fw)
    (x y : ℕ) :
    load fw tail head (R + w * 2 ^ (α * fw)) (α + 1) x y =
      load fw tail head R α x y +
        ∑ e : Fin m, if (head e : ℕ) = α ∧ fld fw R (tail e) = x ∧ w = y then 1 else 0 := by
  unfold load
  rw [← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  rw [fld_add_low fw R w ((S.tail_lt e).trans_le hα)]
  rcases lt_trichotomy (head e : ℕ) α with h | h | h
  · rw [fld_add_low fw R w h, if_neg (fun hh : (head e : ℕ) = α ∧ _ => h.ne hh.1)]
    simp only [h, Nat.lt_succ_of_lt h, true_and, add_zero]
  · rw [h, fld_add_self hR hw, if_neg (fun hh : α < α ∧ _ => lt_irrefl _ hh.1)]
    simp only [Nat.lt_succ_self, true_and, zero_add]
  · rw [if_neg (fun hh : (head e : ℕ) < α + 1 ∧ _ => by have := hh.1; omega),
      if_neg (fun hh : (head e : ℕ) < α ∧ _ => by have := hh.1; omega),
      if_neg (fun hh : (head e : ℕ) = α ∧ _ => h.ne' hh.1)]

/-! ### The minimum -/

theorem best_lt {K : ℕ} (hK : 0 < K) (R α : ℕ) {y : ℕ} (hy : y ≤ K) : best fw Q L tail head R α y < K := by
  induction y with
  | zero => exact hK
  | succ y ih =>
    rw [best]
    split_ifs
    · exact ih (by omega)
    · omega

/-- The word `best` has the minimal `adj`. -/
theorem best_le (R α : ℕ) {y t : ℕ} (ht : t < y) :
    adj fw Q L tail head R α (best fw Q L tail head R α y) ≤ adj fw Q L tail head R α t := by
  induction y with
  | zero => omega
  | succ y ih =>
    rw [best]
    split_ifs with h
    · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h1 | rfl
      · exact ih h1
      · exact h
    · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h1 | rfl
      · exact (not_le.mp h).le.trans (ih h1)
      · exact le_rfl

theorem word_lt (hK : 0 < L ^ Q) (R α : ℕ) : word fw n Q L tail head R α < L ^ Q := by
  unfold word
  split_ifs
  · exact best_lt hK R α le_rfl
  · exact Nat.mod_lt _ hK

theorem score_le (R α y : ℕ) : score fw tail head R α y ≤ m * m := by
  have hl : ∀ x, load fw tail head R α x y ≤ m := fun x => by
    calc load fw tail head R α x y ≤ ∑ _e : Fin m, 1 := sum_le_sum fun e _ => by split_ifs <;> omega
      _ = m := by simp
  calc score fw tail head R α y ≤ ∑ _e : Fin m, m := sum_le_sum fun e _ => by
        split_ifs
        · exact hl _
        · omega
    _ = m * m := by simp

theorem clash_le_zero_iff {R α y : ℕ} :
    clash fw Q L tail head R α y ≤ 0 ↔
      ∀ e : Fin m, (head e : ℕ) = α → ∀ i < Q, dig L (fld fw R (tail e)) i ≠ dig L y i := by
  rw [Nat.le_zero, clash, Finset.sum_eq_zero_iff]
  constructor
  · intro h e he i hi hd
    have h1 := h e (mem_univ _)
    rw [if_pos he, Finset.sum_eq_zero_iff] at h1
    have h2 := h1 i (mem_range.mpr hi)
    rw [if_pos hd] at h2
    omega
  · intro h e _
    by_cases he : (head e : ℕ) = α
    · rw [if_pos he]
      refine Finset.sum_eq_zero fun i hi => if_neg (h e he i (mem_range.mp hi))
    · rw [if_neg he]

/-! ### Half of the words are allowed -/

/-- A letter at a digit is the letter of `1 / L` of the words. -/
theorem card_dig_mul_le {Q L i : ℕ} (hL : 0 < L) (hi : i < Q) (c : ℕ) :
    #{y ∈ range (L ^ Q) | dig L y i = c} * L ≤ L ^ Q := by
  by_cases hc : c < L
  · have h1 : #{y ∈ range (L ^ Q) | dig L y i = c} ≤ #{u : Fin Q → Fin L | u ⟨i, hi⟩ = ⟨c, hc⟩} := by
      refine card_le_card_of_injOn (wordOf hL Q) (fun y hy => ?_) (fun y hy y' hy' he => ?_)
      · have h2 := (mem_filter.mp (mem_coe.mp hy)).2
        exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, Fin.ext h2⟩)
      · have h2 := mem_range.mp (mem_filter.mp (mem_coe.mp hy)).1
        have h3 := mem_range.mp (mem_filter.mp (mem_coe.mp hy')).1
        rw [← wordIdx_wordOf hL h2, ← wordIdx_wordOf hL h3, he]
    have h2 := TransposeBase.card_words_digit (Q := Q) (A := Fin L) ⟨i, hi⟩ ⟨c, hc⟩
    simp only [Fintype.card_fin] at h2
    calc #{y ∈ range (L ^ Q) | dig L y i = c} * L ≤ #{u : Fin Q → Fin L | u ⟨i, hi⟩ = ⟨c, hc⟩} * L :=
          Nat.mul_le_mul_right _ h1
      _ = L ^ Q := h2
  · have h1 : ({y ∈ range (L ^ Q) | dig L y i = c} : Finset ℕ) = ∅ :=
      filter_eq_empty_iff.mpr fun y _ h2 => hc (h2 ▸ dig_lt hL y i)
    rw [h1]
    simp

theorem card_biUnion_mul_le {ι α : Type*} [DecidableEq α] (s : Finset ι) (t : ι → Finset α) (L B : ℕ)
    (h : ∀ a ∈ s, #(t a) * L ≤ B) : #(s.biUnion t) * L ≤ #s * B := by
  calc #(s.biUnion t) * L ≤ (∑ a ∈ s, #(t a)) * L := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ a ∈ s, #(t a) * L := Finset.sum_mul _ _ _
    _ ≤ ∑ _a ∈ s, B := sum_le_sum h
    _ = #s * B := by simp

/-- **At least half of the words are allowed.** -/
theorem card_allowed (S : Shape n D tail head) (hLQ : L = 6 * Q) (hQ : 0 < Q) (R α : ℕ) :
    L ^ Q ≤ 2 * #{y ∈ range (L ^ Q) | clash fw Q L tail head R α y ≤ 0} := by
  classical
  have hL : 0 < L := by omega
  set K := L ^ Q with hK
  have hsub : ({y ∈ range K | ¬ clash fw Q L tail head R α y ≤ 0} : Finset ℕ) ⊆
      ({e | (head e : ℕ) = α} : Finset (Fin m)).biUnion fun e =>
        (range Q).biUnion fun i => {y ∈ range K | dig L y i = dig L (fld fw R (tail e)) i} := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
    rw [clash_le_zero_iff] at hy2
    push Not at hy2
    obtain ⟨e, he, i, hi, hd⟩ := hy2
    refine mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, he⟩, mem_biUnion.mpr ⟨i, mem_range.mpr hi, ?_⟩⟩
    exact mem_filter.mpr ⟨hy1, hd.symm⟩
  have h1 : #{y ∈ range K | ¬ clash fw Q L tail head R α y ≤ 0} * L ≤ 3 * (Q * K) := by
    calc _ ≤ #(({e | (head e : ℕ) = α} : Finset (Fin m)).biUnion fun e =>
          (range Q).biUnion fun i => {y ∈ range K | dig L y i = dig L (fld fw R (tail e)) i}) * L :=
          Nat.mul_le_mul_right _ (card_le_card hsub)
      _ ≤ #({e | (head e : ℕ) = α} : Finset (Fin m)) * (Q * K) := by
          refine card_biUnion_mul_le _ _ _ _ fun e _ => ?_
          refine (card_biUnion_mul_le _ _ _ K fun i hi => ?_).trans (by simp)
          exact card_dig_mul_le hL (mem_range.mp hi) _
      _ ≤ 3 * (Q * K) := Nat.mul_le_mul_right _ (card_head_le S α)
  have h2 := Finset.card_filter_add_card_filter_not (s := range K) (fun y => clash fw Q L tail head R α y ≤ 0)
  rw [card_range] at h2
  have h3 : 2 * #{y ∈ range K | ¬ clash fw Q L tail head R α y ≤ 0} ≤ K := by
    have e : #{y ∈ range K | ¬ clash fw Q L tail head R α y ≤ 0} * L =
        Q * (6 * #{y ∈ range K | ¬ clash fw Q L tail head R α y ≤ 0}) := by
      rw [hLQ]
      ring
    have e2 : 3 * (Q * K) = Q * (3 * K) := by ring
    rw [e, e2] at h1
    have h4 := Nat.le_of_mul_le_mul_left h1 hQ
    omega
  omega

/-- **The word of a node.** It is allowed, and its score is at most the average over the allowed words. -/
theorem score_best_le (S : Shape n D tail head) (hLQ : L = 6 * Q) (hQ : 0 < Q) {R α : ℕ}
    (hR : ∀ u < n, fld fw R u = u % L ^ Q) :
    clash fw Q L tail head R α (best fw Q L tail head R α (L ^ Q)) ≤ 0 ∧
      score fw tail head R α (best fw Q L tail head R α (L ^ Q)) ≤ 6 * capA n (L ^ Q) D / L ^ Q := by
  classical
  have hL : 0 < L := by omega
  have hK : 0 < L ^ Q := by positivity
  set b := best fw Q L tail head R α (L ^ Q) with hb
  set A := ({y ∈ range (L ^ Q) | clash fw Q L tail head R α y ≤ 0} : Finset ℕ) with hA
  have hcard : L ^ Q ≤ 2 * #A := card_allowed S hLQ hQ R α
  have hmin : ∀ y ∈ A, adj fw Q L tail head R α b ≤ score fw tail head R α y := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_filter.mp hy
    have h1 := best_le (fw := fw) (Q := Q) (L := L) (tail := tail) (head := head) R α (mem_range.mp hy1)
    have e : adj fw Q L tail head R α y = score fw tail head R α y := if_pos hy2
    rwa [e, ← hb] at h1
  have hne : A.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hallow : clash fw Q L tail head R α b ≤ 0 := by
    obtain ⟨y, hy⟩ := hne
    have h1 := (hmin y hy).trans (score_le R α y)
    by_contra hc
    rw [adj, if_neg hc] at h1
    omega
  have hadj : adj fw Q L tail head R α b = score fw tail head R α b := if_pos hallow
  refine ⟨hallow, (Nat.le_div_iff_mul_le hK).mpr ?_⟩
  have h1 : score fw tail head R α b * #A ≤ ∑ y ∈ A, score fw tail head R α y := by
    calc score fw tail head R α b * #A = ∑ _y ∈ A, score fw tail head R α b := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum fun y hy => hadj ▸ hmin y hy
  have h2 : ∑ y ∈ A, score fw tail head R α y ≤ ∑ y ∈ range (L ^ Q), score fw tail head R α y :=
    Finset.sum_le_sum_of_subset (filter_subset _ _)
  have h3 := sum_score_le (K := L ^ Q) S (α := α) hR
  calc score fw tail head R α b * L ^ Q ≤ score fw tail head R α b * (2 * #A) := Nat.mul_le_mul_left _ hcard
    _ = 2 * (score fw tail head R α b * #A) := by ring
    _ ≤ 6 * capA n (L ^ Q) D := by omega

/-! ### The fields of the table -/

theorem table_lt (hK : 0 < L ^ Q) (hK2 : L ^ Q ≤ 2 ^ fw) (α : ℕ) :
    table fw n Q L tail head α < 2 ^ (α * fw) := by
  induction α with
  | zero => simp [table]
  | succ α ih => exact add_mul_lt ih ((word_lt hK _ _).trans_le hK2)

theorem fld_table_self (hK : 0 < L ^ Q) (hK2 : L ^ Q ≤ 2 ^ fw) (α : ℕ) :
    fld fw (table fw n Q L tail head (α + 1)) α = word fw n Q L tail head (table fw n Q L tail head α) α :=
  fld_add_self (table_lt hK hK2 α) ((word_lt hK _ _).trans_le hK2)

/-- A field is not changed by the later nodes. -/
theorem fld_table_stable {u α β : ℕ} (hu : u < α) (hαβ : α ≤ β) :
    fld fw (table fw n Q L tail head β) u = fld fw (table fw n Q L tail head α) u := by
  induction β, hαβ using Nat.le_induction with
  | base => rfl
  | succ β hβ ih =>
    rw [← ih]
    exact fld_add_low fw _ _ (hu.trans_le hβ)

theorem fld_table_eq (hK : 0 < L ^ Q) (hK2 : L ^ Q ≤ 2 ^ fw) {u α : ℕ} (hu : u < α) :
    fld fw (table fw n Q L tail head α) u = word fw n Q L tail head (table fw n Q L tail head u) u := by
  rw [fld_table_stable (Nat.lt_succ_self u) hu, fld_table_self hK hK2]

theorem fld_table_lt (hK : 0 < L ^ Q) (hK2 : L ^ Q ≤ 2 ^ fw) {u α : ℕ} (hu : u < α) :
    fld fw (table fw n Q L tail head α) u < L ^ Q := by
  rw [fld_table_eq hK hK2 hu]
  exact word_lt hK _ _

/-- A node below `n` has the word `u % L ^ Q`. -/
theorem fld_table_var (hK : 0 < L ^ Q) (hK2 : L ^ Q ≤ 2 ^ fw) {u α : ℕ} (hun : u < n) (hu : u < α) :
    fld fw (table fw n Q L tail head α) u = u % L ^ Q := by
  rw [fld_table_eq hK hK2 hu, word, if_neg (by omega)]

/-! ### The loads stay small -/

/-- **All loads stay small**, by induction on the node. -/
theorem load_table_le (S : Shape n D tail head) (hLQ : L = 6 * Q) (hQ : 0 < Q) (hK2 : L ^ Q ≤ 2 ^ fw) (α x y : ℕ) :
    load fw tail head (table fw n Q L tail head α) α x y ≤ capB n (L ^ Q) D := by
  have hL : 0 < L := by omega
  have hK : 0 < L ^ Q := by positivity
  induction α generalizing x y with
  | zero =>
    rw [load_eq_zero S (Nat.zero_le n)]
    exact Nat.zero_le _
  | succ α ih =>
    by_cases hα : n ≤ α
    · set R := table fw n Q L tail head α with hRdef
      have hR : ∀ u < n, fld fw R u = u % L ^ Q := fun u hu =>
        fld_table_var hK hK2 hu (hu.trans_le hα)
      have ew : word fw n Q L tail head R α = best fw Q L tail head R α (L ^ Q) := if_pos hα
      have ht : table fw n Q L tail head (α + 1) = R + best fw Q L tail head R α (L ^ Q) * 2 ^ (α * fw) := by
        show R + word fw n Q L tail head R α * 2 ^ (α * fw) = _
        rw [ew]
      have hw : best fw Q L tail head R α (L ^ Q) < 2 ^ fw := (best_lt hK R α le_rfl).trans_le hK2
      have hRlt : R < 2 ^ (α * fw) := table_lt hK hK2 α
      rw [ht, load_step S hα hRlt hw]
      set w := best fw Q L tail head R α (L ^ Q) with hwdef
      by_cases hz : ∃ e0 : Fin m, (head e0 : ℕ) = α ∧ fld fw R (tail e0) = x ∧ w = y
      · obtain ⟨e0, h1, rfl, rfl⟩ := hz
        have h2 : load fw tail head R α (fld fw R (tail e0)) w ≤ score fw tail head R α w := by
          have := single_le_sum (s := univ) (f := fun e : Fin m =>
            if (head e : ℕ) = α then load fw tail head R α (fld fw R (tail e)) w else 0)
            (fun _ _ => Nat.zero_le _) (mem_univ e0)
          simp only [if_pos h1] at this
          exact this
        have h3 := (score_best_le (R := R) (α := α) S hLQ hQ hR).2
        rw [← hwdef] at h3
        have h4 : ∑ e : Fin m, (if (head e : ℕ) = α ∧ fld fw R (tail e) = fld fw R (tail e0) ∧ w = w then 1 else 0) ≤ 3 := by
          refine le_trans ?_ (card_head_le S α)
          rw [card_filter]
          refine sum_le_sum fun e _ => ?_
          by_cases h : (head e : ℕ) = α
          · rw [if_pos h]
            split_ifs <;> omega
          · rw [if_neg h, if_neg (fun hh => h hh.1)]
        rw [capB]
        omega
      · have h0 : ∑ e : Fin m, (if (head e : ℕ) = α ∧ fld fw R (tail e) = x ∧ w = y then 1 else 0) = 0 :=
          sum_eq_zero fun e _ => if_neg fun h => hz ⟨e, h⟩
        rw [h0, add_zero]
        exact ih x y
    · rw [load_eq_zero S (by omega)]
      exact Nat.zero_le _

/-- The bound on the loads, for `K ^ 2 ≤ n`. -/
theorem sq_mul_capB_le {K : ℕ} (hn : K ^ 2 ≤ n) (hD : 3 ≤ D) : K ^ 2 * capB n K D ≤ 13 * D * n := by
  have h1 : K * capA n K D ≤ (n + K) * D := by
    rw [capA, ← mul_assoc, Nat.mul_add, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_div_le n K) K)
  have h2 : K * (6 * capA n K D / K) ≤ 6 * capA n K D := Nat.mul_div_le _ _
  have h3 : K ≤ n := (Nat.le_self_pow (by norm_num) K).trans hn
  have h4 : K ^ 2 * capB n K D ≤ 6 * ((n + K) * D) + 3 * K ^ 2 := by
    calc K ^ 2 * capB n K D = K * (K * (6 * capA n K D / K)) + 3 * K ^ 2 := by
          rw [capB]
          ring
      _ ≤ K * (6 * capA n K D) + 3 * K ^ 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ h2) _
      _ = 6 * (K * capA n K D) + 3 * K ^ 2 := by ring
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) _
  have h5 : (n + K) * D ≤ (2 * n) * D := Nat.mul_le_mul_right _ (by omega)
  have h6 : 3 * n ≤ D * n := Nat.mul_le_mul_right _ hD
  have e : 13 * D * n = 6 * ((2 * n) * D) + D * n := by ring
  omega

/-! ### The wires -/

/-- The word of a node, for the table `R`. -/
def wdOf {Q L : ℕ} (hL : 0 < L) (fw R : ℕ) (α : Fin v) : Fin Q → Fin L := wordOf hL Q (fld fw R α)

/-- The layer of a wire: the number of earlier wires with the same tail word and head word. -/
def layN (fw R : ℕ) (tail head : Fin m → Fin v) (e : Fin m) : ℕ :=
  ∑ e' : Fin m, if e' < e ∧ fld fw R (tail e') = fld fw R (tail e) ∧ fld fw R (head e') = fld fw R (head e) then 1 else 0

theorem layN_eq_card (fw R : ℕ) (tail head : Fin m → Fin v) (e : Fin m) :
    layN fw R tail head e =
      #{e' | e' < e ∧ fld fw R (tail e') = fld fw R (tail e) ∧ fld fw R (head e') = fld fw R (head e)} := by
  rw [layN, card_filter]

/-- A wire is counted by the layer of a later wire with the same words. -/
theorem layN_lt_of_lt {R : ℕ} {e e' : Fin m} (hlt : e' < e) (h1 : fld fw R (tail e') = fld fw R (tail e))
    (h2 : fld fw R (head e') = fld fw R (head e)) : layN fw R tail head e' < layN fw R tail head e := by
  rw [layN_eq_card, layN_eq_card]
  refine card_lt_card ⟨fun a ha => ?_, fun hsub => ?_⟩
  · obtain ⟨-, a1, a2, a3⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_univ _, a1.trans hlt, a2.trans h1, a3.trans h2⟩
  · have := hsub (mem_filter.mpr ⟨mem_univ _, hlt, h1, h2⟩)
    exact lt_irrefl _ (mem_filter.mp this).2.1

/-- The layer is below the bound on the loads. -/
theorem layN_lt (S : Shape n D tail head) (hLQ : L = 6 * Q) (hQ : 0 < Q) (hK2 : L ^ Q ≤ 2 ^ fw) (e : Fin m) :
    layN fw (table fw n Q L tail head v) tail head e < capB n (L ^ Q) D := by
  classical
  set R := table fw n Q L tail head v with hR
  have h1 := load_table_le (α := v) (x := fld fw R (tail e)) (y := fld fw R (head e)) S hLQ hQ hK2
  rw [← hR] at h1
  refine lt_of_lt_of_le ?_ h1
  rw [layN_eq_card, load, ← card_filter]
  refine card_lt_card ⟨fun a ha => ?_, fun hsub => ?_⟩
  · obtain ⟨-, a1, a2, a3⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_univ _, (head a).2, a2, a3⟩
  · have := hsub (mem_filter.mpr ⟨mem_univ _, (head e).2, rfl, rfl⟩)
    exact lt_irrefl _ (mem_filter.mp this).2.1

/-- A word determines its number, for numbers below `L ^ Q`. -/
theorem word_inj {Q L x y : ℕ} (hL : 0 < L) (hx : x < L ^ Q) (hy : y < L ^ Q)
    (h : wordOf hL Q x = wordOf hL Q y) : x = y := by
  rw [← wordIdx_wordOf hL hx, ← wordIdx_wordOf hL hy, h]

/-- The head of a wire has a word that differs in every digit from the word of the tail. -/
theorem differ_table (S : Shape n D tail head) (hLQ : L = 6 * Q) (hQ : 0 < Q) (hK2 : L ^ Q ≤ 2 ^ fw) (e : Fin m)
    {i : ℕ} (hi : i < Q) :
    dig L (fld fw (table fw n Q L tail head v) (tail e)) i ≠ dig L (fld fw (table fw n Q L tail head v) (head e)) i := by
  have hL : 0 < L := by omega
  have hK : 0 < L ^ Q := by positivity
  have hα : n ≤ (head e : ℕ) := S.le_head e
  have hv : (head e : ℕ) < v := (head e).2
  set α : ℕ := (head e : ℕ) with hαdef
  set R := table fw n Q L tail head α with hRdef
  have hR : ∀ u < n, fld fw R u = u % L ^ Q := fun u hu =>
    fld_table_var hK hK2 hu (hu.trans_le hα)
  have h1 := (score_best_le (R := R) (α := α) S hLQ hQ hR).1
  rw [clash_le_zero_iff] at h1
  have h2 : fld fw (table fw n Q L tail head v) α = best fw Q L tail head R α (L ^ Q) := by
    rw [fld_table_eq hK hK2 hv, word, if_pos hα]
  have h3 : fld fw (table fw n Q L tail head v) (tail e) = fld fw R (tail e) :=
    fld_table_stable ((S.tail_lt e).trans_le hα) hv.le
  rw [h2, h3]
  exact h1 e rfl i hi

/-- **The wires** of a network on the words of its nodes. The layers separate the wires between two words. -/
def wiresOf (S : Shape n D tail head) (hLQ : L = 6 * Q) (hQ : 0 < Q) (hK2 : L ^ Q ≤ 2 ^ fw) :
    OnePigeonhole.Wires Q L (capB n (L ^ Q) D) m where
  tw e := wdOf (by omega) fw (table fw n Q L tail head v) (tail e)
  hw e := wdOf (by omega) fw (table fw n Q L tail head v) (head e)
  lay e := ⟨layN fw (table fw n Q L tail head v) tail head e, layN_lt S hLQ hQ hK2 e⟩
  differ e t h := differ_table S hLQ hQ hK2 e t.2 (congrArg Fin.val h)
  inj := by
    intro e e' he
    have hL : 0 < L := by omega
    have hK : 0 < L ^ Q := by positivity
    have h1 := (Prod.mk.inj he).1
    have h2 := (Prod.mk.inj (Prod.mk.inj he).2).1
    have h3 := congrArg Fin.val (Prod.mk.inj (Prod.mk.inj he).2).2
    have h4 := word_inj hL (fld_table_lt hK hK2 (tail e).2) (fld_table_lt hK hK2 (tail e').2) h1
    have h5 := word_inj hL (fld_table_lt hK hK2 (head e).2) (fld_table_lt hK hK2 (head e').2) h2
    simp only at h3
    rcases lt_trichotomy e e' with h6 | h6 | h6
    · exact absurd h3 (layN_lt_of_lt h6 h4 h5).ne
    · exact h6
    · exact absurd h3 (layN_lt_of_lt h6 h4.symm h5.symm).ne'

/-- The words of the wires are the words of their tail and their head. -/
theorem onNodes_wiresOf (S : Shape n D tail head) (hLQ : L = 6 * Q) (hQ : 0 < Q) (hK2 : L ^ Q ≤ 2 ^ fw) :
    OnePigeonhole.OnNodes (wiresOf S hLQ hQ hK2) tail head
      (wdOf (by omega) fw (table fw n Q L tail head v)) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

end OnePigeonhole.Greedy
