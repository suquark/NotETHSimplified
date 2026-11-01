import UncrossingWires.Base
import UncrossingWires.Chain
import TransposeBase.Pseudo.PlaceCore

/-!
# The greedy placement

The placement of the paper (Lemma `lem:count`), on numbers. A network has the wires `e : Fin m` and the nodes `Fin v`. The
tail of each wire is a node below `n`, and the head of each wire is a node at least `n` (`Shape`).

* A node `α < n` gets the word `α % K`.
* The other nodes are placed in the order of their numbers. Let `R` be the table of the words of the nodes below `α`, one
  field for each node. `load x y` is the number of wires with head below `α`, tail word `x` and head word `y`. The node
  `α` gets the word `y < K` that minimizes `score y`, the sum of `load (word of tail e) y` over the wires `e` with head
  `α`, with the smallest such `y` on ties.

`table α` is the table of the words of the nodes below `α`, by recursion on `α`.

`load_table_le`: all loads stay at most `capB n K D = 3 * capA n K D / K + 3`, where `capA n K D = (n / K + 1) * D` bounds
the number of wires with the tail on one word.

`psi_table_le_all`: for every `n`, the potential of the first level satisfies `K ^ 2 * psi K N.w0 ≤ (4 * D * (n + K ^ 2)) ^ 2`.
`psi_table_le`: for `K ^ 2 ≤ n`, the sharper bound `K ^ 2 * psi K N.w0 ≤ 28 * (D * n) ^ 2`, which the program uses.
-/

namespace UncrossingWires.Greedy

open Finset
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

variable (fw n K : ℕ) (tail head : Fin m → Fin v)

/-- The number of wires with head below `α`, tail word `x` and head word `y`, for the words in the table `R`. -/
def load (R α x y : ℕ) : ℕ :=
  ∑ e : Fin m, if (head e : ℕ) < α ∧ fld fw R (tail e) = x ∧ fld fw R (head e) = y then 1 else 0

/-- The number that the node `α` minimizes: the sum of the loads from the words of its tails towards the word `y`. -/
def score (R α y : ℕ) : ℕ :=
  ∑ e : Fin m, if (head e : ℕ) = α then load fw tail head R α (fld fw R (tail e)) y else 0

/-- The first word with the minimal score among the words below `y`. -/
def best (R α : ℕ) : ℕ → ℕ
  | 0 => 0
  | y + 1 => if score fw tail head R α (best R α y) ≤ score fw tail head R α y then best R α y else y

/-- The word of the node `α`, for the table `R` of the nodes below `α`. -/
def word (R α : ℕ) : ℕ := if n ≤ α then best fw tail head R α K else α % K

/-- The table of the words of the nodes below `α`, with fields of width `fw`. -/
def table : ℕ → ℕ
  | 0 => 0
  | α + 1 => table α + word fw n K tail head (table α) α * 2 ^ (α * fw)

end Defs

/-- The number of wires with the tail on one word is at most this. -/
def capA (n K D : ℕ) : ℕ := (n / K + 1) * D

/-- All loads are at most this. -/
def capB (n K D : ℕ) : ℕ := 3 * capA n K D / K + 3

variable {fw n K D : ℕ} {tail head : Fin m → Fin v}

/-! ### The minimum -/

theorem best_lt (hK : 0 < K) (R α : ℕ) {y : ℕ} (hy : y ≤ K) : best fw tail head R α y < K := by
  induction y with
  | zero => exact hK
  | succ y ih =>
    rw [best]
    split_ifs
    · exact ih (by omega)
    · omega

/-- The word `best` has the minimal score. -/
theorem best_le (R α : ℕ) {y t : ℕ} (ht : t < y) :
    score fw tail head R α (best fw tail head R α y) ≤ score fw tail head R α t := by
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

/-- The smaller words have a larger score. -/
theorem best_first (R α : ℕ) {y t : ℕ} (ht : t < best fw tail head R α y) :
    score fw tail head R α (best fw tail head R α y) < score fw tail head R α t := by
  induction y with
  | zero => exact absurd ht (Nat.not_lt_zero _)
  | succ y ih =>
    rw [best] at ht ⊢
    by_cases h : score fw tail head R α (best fw tail head R α y) ≤ score fw tail head R α y
    · rw [if_pos h] at ht ⊢
      exact ih ht
    · rw [if_neg h] at ht ⊢
      exact (not_le.mp h).trans_le (best_le R α ht)

theorem word_lt (hK : 0 < K) (R α : ℕ) : word fw n K tail head R α < K := by
  unfold word
  split_ifs
  · exact best_lt hK R α le_rfl
  · exact Nat.mod_lt _ hK

/-! ### The fields of the table -/

theorem table_lt (hK : 0 < K) (hK2 : K ≤ 2 ^ fw) (α : ℕ) : table fw n K tail head α < 2 ^ (α * fw) := by
  induction α with
  | zero => simp [table]
  | succ α ih => exact add_mul_lt ih ((word_lt hK _ _).trans_le hK2)

theorem fld_table_self (hK : 0 < K) (hK2 : K ≤ 2 ^ fw) (α : ℕ) :
    fld fw (table fw n K tail head (α + 1)) α = word fw n K tail head (table fw n K tail head α) α :=
  fld_add_self (table_lt hK hK2 α) ((word_lt hK _ _).trans_le hK2)

/-- A field is not changed by the later nodes. -/
theorem fld_table_stable {u α β : ℕ} (hu : u < α) (hαβ : α ≤ β) :
    fld fw (table fw n K tail head β) u = fld fw (table fw n K tail head α) u := by
  induction β, hαβ using Nat.le_induction with
  | base => rfl
  | succ β hβ ih =>
    rw [← ih]
    exact fld_add_low fw _ _ (hu.trans_le hβ)

theorem fld_table_eq (hK : 0 < K) (hK2 : K ≤ 2 ^ fw) {u α : ℕ} (hu : u < α) :
    fld fw (table fw n K tail head α) u = word fw n K tail head (table fw n K tail head u) u := by
  rw [fld_table_stable (Nat.lt_succ_self u) hu, fld_table_self hK hK2]

theorem fld_table_lt (hK : 0 < K) (hK2 : K ≤ 2 ^ fw) {u α : ℕ} (hu : u < α) :
    fld fw (table fw n K tail head α) u < K := by
  rw [fld_table_eq hK hK2 hu]
  exact word_lt hK _ _

/-- A node below `n` has the word `u % K`. -/
theorem fld_table_var (hK : 0 < K) (hK2 : K ≤ 2 ^ fw) {u α : ℕ} (hun : u < n) (hu : u < α) :
    fld fw (table fw n K tail head α) u = u % K := by
  rw [fld_table_eq hK hK2 hu, word, if_neg (by omega)]

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
theorem card_tail_word_le (S : Shape n D tail head) (x : ℕ) :
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
theorem sum_load_le (S : Shape n D tail head) {R α : ℕ} (hR : ∀ u < n, fld fw R u = u % K) (x : ℕ) :
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
theorem sum_score_le (S : Shape n D tail head) {R α : ℕ} (hR : ∀ u < n, fld fw R u = u % K) :
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

/-- The minimal score is at most the average. -/
theorem score_best_le (S : Shape n D tail head) (hK : 0 < K) {R α : ℕ} (hR : ∀ u < n, fld fw R u = u % K) :
    score fw tail head R α (best fw tail head R α K) ≤ 3 * capA n K D / K := by
  rw [Nat.le_div_iff_mul_le hK]
  calc score fw tail head R α (best fw tail head R α K) * K
      = ∑ _y ∈ range K, score fw tail head R α (best fw tail head R α K) := by
        rw [sum_const, card_range, smul_eq_mul, mul_comm]
    _ ≤ ∑ y ∈ range K, score fw tail head R α y :=
        sum_le_sum fun y hy => best_le R α (mem_range.mp hy)
    _ ≤ _ := sum_score_le S hR

/-! ### The loads stay small -/

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

/-- **All loads stay small**, by induction on the node. -/
theorem load_table_le (S : Shape n D tail head) (hK : 0 < K) (hK2 : K ≤ 2 ^ fw) (α x y : ℕ) :
    load fw tail head (table fw n K tail head α) α x y ≤ capB n K D := by
  induction α generalizing x y with
  | zero =>
    rw [load_eq_zero S (Nat.zero_le n)]
    exact Nat.zero_le _
  | succ α ih =>
    by_cases hα : n ≤ α
    · set R := table fw n K tail head α with hRdef
      have hR : ∀ u < n, fld fw R u = u % K := fun u hu =>
        fld_table_var hK hK2 hu (hu.trans_le hα)
      have ew : word fw n K tail head R α = best fw tail head R α K := if_pos hα
      have ht : table fw n K tail head (α + 1) = R + best fw tail head R α K * 2 ^ (α * fw) := by
        show R + word fw n K tail head R α * 2 ^ (α * fw) = _
        rw [ew]
      have hw : best fw tail head R α K < 2 ^ fw := (best_lt hK R α le_rfl).trans_le hK2
      have hRlt : R < 2 ^ (α * fw) := table_lt hK hK2 α
      rw [ht, load_step S hα hRlt hw]
      set w := best fw tail head R α K with hwdef
      by_cases hz : ∃ e0 : Fin m, (head e0 : ℕ) = α ∧ fld fw R (tail e0) = x ∧ w = y
      · obtain ⟨e0, h1, rfl, rfl⟩ := hz
        have h2 : load fw tail head R α (fld fw R (tail e0)) w ≤ score fw tail head R α w := by
          have := single_le_sum (s := univ) (f := fun e : Fin m =>
            if (head e : ℕ) = α then load fw tail head R α (fld fw R (tail e)) w else 0)
            (fun _ _ => Nat.zero_le _) (mem_univ e0)
          simp only [if_pos h1] at this
          exact this
        have h3 := score_best_le (α := α) S hK hR
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

/-! ### The potential -/

/-- The wires between the words `x` and `y` are counted by two loads. -/
theorem w0_le_load (N : BaseNet m v) {R : ℕ} (hr : ∀ α, N.rOf α = fld fw R α) (x y : ℕ) :
    N.w0 x y ≤ load fw N.tail N.head R v x y + load fw N.tail N.head R v y x := by
  rw [BaseNet.w0, Finset.sum_range]
  unfold load
  rw [← sum_add_distrib]
  refine sum_le_sum fun e _ => ?_
  have h0 : (N.head e : ℕ) < v := (N.head e).2
  by_cases hj : N.joins e x y
  · rw [if_pos hj]
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [N.tw_val, hr] at h1
      rw [N.hw_val, hr] at h2
      rw [if_pos (⟨h0, h1, h2⟩ : _ ∧ _ ∧ _)]
      omega
    · rw [N.tw_val, hr] at h1
      rw [N.hw_val, hr] at h2
      rw [if_pos (⟨h0, h1, h2⟩ : _ ∧ _ ∧ _)]
      omega
  · rw [if_neg hj]
    omega

/-- The potential, from a bound on the weights and a bound on their sum. -/
theorem psi_bound {K T m Z : ℕ} {w : ℕ → ℕ → ℕ} (hw : ∀ x y, w x y ≤ 2 * T)
    (htot : ∑ x ∈ range K, ∑ y ∈ range K, w x y ≤ 2 * m) (hKT : K ^ 2 * T ≤ Z) :
    K ^ 2 * psi K w ≤ 4 * m * Z := by
  have h1 : psi K w ≤ 2 * T * (2 * m) := by
    unfold psi
    calc ∑ x ∈ range K, ∑ y ∈ range K, w x y ^ 2
        ≤ ∑ x ∈ range K, ∑ y ∈ range K, 2 * T * w x y :=
          sum_le_sum fun x _ => sum_le_sum fun y _ => by
            rw [sq]
            exact Nat.mul_le_mul_right _ (hw x y)
      _ = 2 * T * ∑ x ∈ range K, ∑ y ∈ range K, w x y := by simp only [mul_sum]
      _ ≤ _ := Nat.mul_le_mul_left _ htot
  calc K ^ 2 * psi K w ≤ K ^ 2 * (2 * T * (2 * m)) := Nat.mul_le_mul_left _ h1
    _ = 4 * m * (K ^ 2 * T) := by ring
    _ ≤ 4 * m * Z := Nat.mul_le_mul_left _ hKT

/-- The bound on the loads, for `K ^ 2 ≤ n`. -/
theorem sq_mul_capB_le (hn : K ^ 2 ≤ n) (hD : 3 ≤ D) : K ^ 2 * capB n K D ≤ 7 * D * n := by
  have h1 : K * capA n K D ≤ (n + K) * D := by
    rw [capA, ← mul_assoc, Nat.mul_add, mul_one]
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_div_le n K) K)
  have h2 : K * (3 * capA n K D / K) ≤ 3 * capA n K D := Nat.mul_div_le _ _
  have h3 : K ≤ n := (Nat.le_self_pow (by norm_num) K).trans hn
  have h4 : K ^ 2 * capB n K D ≤ 3 * ((n + K) * D) + 3 * K ^ 2 := by
    calc K ^ 2 * capB n K D = K * (K * (3 * capA n K D / K)) + 3 * K ^ 2 := by
          rw [capB]
          ring
      _ ≤ K * (3 * capA n K D) + 3 * K ^ 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ h2) _
      _ = 3 * (K * capA n K D) + 3 * K ^ 2 := by ring
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) _
  have h5 : (n + K) * D ≤ (2 * n) * D := Nat.mul_le_mul_right _ (by omega)
  have h6 : 3 * n ≤ D * n := Nat.mul_le_mul_right _ hD
  have e : 7 * D * n = 3 * ((2 * n) * D) + D * n := by ring
  omega

/-- **The potential of the first level**, for the words of the greedy table. -/
theorem psi_table_le {N : BaseNet m v} (S : Shape n D N.tail N.head) (hK : 0 < K) (hK2 : K ≤ 2 ^ fw)
    (hr : ∀ α, N.rOf α = fld fw (table fw n K N.tail N.head v) α) (hn : K ^ 2 ≤ n) (hD : 3 ≤ D) (hm : m ≤ D * n) :
    K ^ 2 * psi K N.w0 ≤ 28 * (D * n) ^ 2 := by
  have hrK : ∀ α, N.rOf α < K := fun α => by
    rw [hr]
    exact fld_table_lt hK hK2 α.2
  have h1 := psi_bound (K := K) (T := capB n K D) (Z := 7 * D * n) (w := N.w0) (fun x y => by
      have h2 := w0_le_load N hr x y
      have h3 := load_table_le S hK hK2 v x y
      have h4 := load_table_le S hK hK2 v y x
      omega) (N.w0_total hrK) (sq_mul_capB_le hn hD)
  calc K ^ 2 * psi K N.w0 ≤ 4 * m * (7 * D * n) := h1
    _ ≤ 4 * (D * n) * (7 * D * n) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)
    _ = 28 * (D * n) ^ 2 := by ring

/-- The bound on the loads, for every `n`. -/
theorem sq_mul_capB_le_all (hK : 0 < K) (hD : 3 ≤ D) : K ^ 2 * capB n K D ≤ D * (3 * n + 4 * K ^ 2) := by
  have h1 : K * (3 * capA n K D / K) ≤ 3 * capA n K D := Nat.mul_div_le _ _
  have h2 : K * (n / K) ≤ n := Nat.mul_div_le _ _
  have h3 : K ≤ K ^ 2 := by nlinarith
  have h4 : K * capA n K D ≤ (n + K) * D := by
    unfold capA
    calc K * ((n / K + 1) * D) = (K * (n / K) + K) * D := by ring
      _ ≤ (n + K) * D := Nat.mul_le_mul_right _ (by omega)
  unfold capB
  calc K ^ 2 * (3 * capA n K D / K + 3)
      = K * (K * (3 * capA n K D / K)) + 3 * K ^ 2 := by ring
    _ ≤ K * (3 * capA n K D) + 3 * K ^ 2 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) _
    _ = 3 * (K * capA n K D) + 3 * K ^ 2 := by ring
    _ ≤ 3 * ((n + K) * D) + D * K ^ 2 := by
        exact Nat.add_le_add (Nat.mul_le_mul_left _ h4) (Nat.mul_le_mul_right _ hD)
    _ ≤ D * (3 * n + 4 * K ^ 2) := by nlinarith

/-- **The potential of the first level, for every `n`.** The square of the potential is at most `(4 * D * (n + K ^ 2)) ^ 2`.
This is the bound of the paper; `psi_table_le` is the sharper form for large `n` that the program uses. -/
theorem psi_table_le_all {N : BaseNet m v} (S : Shape n D N.tail N.head) (hK : 0 < K) (hK2 : K ≤ 2 ^ fw)
    (hr : ∀ α, N.rOf α = fld fw (table fw n K N.tail N.head v) α) (hD : 3 ≤ D) (hm : m ≤ D * n) :
    K ^ 2 * psi K N.w0 ≤ (4 * D * (n + K ^ 2)) ^ 2 := by
  have hrK : ∀ α, N.rOf α < K := fun α => by
    rw [hr]
    exact fld_table_lt hK hK2 α.2
  have h1 := psi_bound (K := K) (T := capB n K D) (Z := D * (3 * n + 4 * K ^ 2)) (w := N.w0) (fun x y => by
      have h2 := w0_le_load N hr x y
      have h3 := load_table_le S hK hK2 v x y
      have h4 := load_table_le S hK hK2 v y x
      omega) (N.w0_total hrK) (sq_mul_capB_le_all hK hD)
  calc K ^ 2 * psi K N.w0 ≤ 4 * m * (D * (3 * n + 4 * K ^ 2)) := h1
    _ ≤ 4 * (D * n) * (D * (3 * n + 4 * K ^ 2)) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)
    _ ≤ (4 * D * (n + K ^ 2)) ^ 2 := by
        have e : (4 * D * (n + K ^ 2)) ^ 2 = 4 * (D * n) * (D * (3 * n + 4 * K ^ 2)) + D ^ 2 * (4 * n ^ 2 + 16 * n * K ^ 2 + 16 * K ^ 4) := by ring
        rw [e]
        exact Nat.le_add_right _ _

end UncrossingWires.Greedy
