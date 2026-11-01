import SatBase.CoreBranching
import Mathlib

/-!
# Formulas as bitset words: the specification

A clause with at most three literals has a code below `(2 * n + 1) ^ 3`. The digits of the code in base
`2 * n + 1` are the literal codes in increasing order, with `0` as padding in the low digits. A formula is the
word with a bit for each clause code. This file holds only specifications.

* `litCode (v, b) = 2 * v + b + 1`, between `1` and `2 * n`.
* `decode n k`: the literals whose code is a digit of `k`.
* `ValidC n k`: the digits of `k` are sorted, and strictly increasing where they are not zero.
* `code n C`: the valid code of `C`. `code` and `decode` are inverse (`code_spec`, `valid_unique`).
* `encF n F = ∑ C ∈ F, 2 ^ code n C`.
-/

namespace TransposeBase.Pseudo.CnfTree

open SatBase Finset

/-! ### Indicators -/

open Classical in
/-- The indicator of a proposition, as a number. -/
noncomputable def ind (p : Prop) : ℕ := if p then 1 else 0

theorem ind_pos {p : Prop} (h : p) : ind p = 1 := by simp [ind, h]
theorem ind_neg {p : Prop} (h : ¬p) : ind p = 0 := by simp [ind, h]
theorem ind_le_one (p : Prop) : ind p ≤ 1 := by unfold ind; split <;> simp
theorem ind_ne_zero {p : Prop} : ind p ≠ 0 ↔ p := by unfold ind; split <;> simp [*]
theorem ind_eq_zero {p : Prop} : ind p = 0 ↔ ¬p := by unfold ind; split <;> simp [*]
theorem ind_congr {p q : Prop} (h : p ↔ q) : ind p = ind q := by rw [propext h]
theorem ind_eq_iff {p q : Prop} : ind p = ind q ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [ind, hp, hq]

/-! ### Literals -/

/-- The code of a literal, between `1` and `2 * n`. -/
def litCode {n : ℕ} (l : SignedLiteral n) : ℕ := 2 * (l.1 : ℕ) + l.2.toNat + 1

theorem litCode_pos {n : ℕ} (l : SignedLiteral n) : 0 < litCode l := by simp [litCode]

theorem litCode_le {n : ℕ} (l : SignedLiteral n) : litCode l ≤ 2 * n := by
  obtain ⟨v, b⟩ := l
  have := v.2
  have : b.toNat ≤ 1 := by cases b <;> simp
  simp only [litCode]
  omega

theorem litCode_injective {n : ℕ} : Function.Injective (litCode (n := n)) := by
  rintro ⟨v, b⟩ ⟨w, c⟩ h
  simp only [litCode] at h
  have hb : b.toNat ≤ 1 := by cases b <;> simp
  have hc : c.toNat ≤ 1 := by cases c <;> simp
  have h1 : v = w := Fin.ext (by omega)
  have h2 : b = c := by cases b <;> cases c <;> simp at h ⊢ <;> omega
  rw [h1, h2]

/-- The literal with code `c + 1`. -/
theorem exists_lit {n c : ℕ} (h : c < 2 * n) : ∃ l : SignedLiteral n, litCode l = c + 1 := by
  refine ⟨(⟨c / 2, by omega⟩, decide (c % 2 = 1)), ?_⟩
  rcases Nat.mod_two_eq_zero_or_one c with h2 | h2 <;> simp [litCode, h2] <;> omega

theorem forall_lit_iff {n : ℕ} (P : ℕ → Prop) :
    (∀ l : SignedLiteral n, P (litCode l)) ↔ ∀ c < 2 * n, P (c + 1) := by
  constructor
  · intro h c hc
    obtain ⟨l, hl⟩ := exists_lit hc
    rw [← hl]
    exact h l
  · intro h l
    have h1 := litCode_pos l
    have h2 := litCode_le l
    have := h (litCode l - 1) (by omega)
    rwa [Nat.sub_add_cancel h1] at this

open Classical in
theorem card_filter_lit {n : ℕ} (Q : ℕ → Prop) :
    (univ.filter (fun l : SignedLiteral n => Q (litCode l))).card =
      ∑ c ∈ range (2 * n), ind (Q (c + 1)) := by
  have h1 : ∑ c ∈ range (2 * n), ind (Q (c + 1)) = ((range (2 * n)).filter fun c => Q (c + 1)).card := by
    rw [card_filter]
    rfl
  rw [h1]
  apply Finset.card_bij (fun l _ => litCode l - 1)
  · intro l hl
    have h1 := litCode_pos l
    have h2 := litCode_le l
    simp only [mem_filter, mem_univ, true_and, mem_range] at hl ⊢
    rw [Nat.sub_add_cancel h1]
    exact ⟨by omega, hl⟩
  · intro a _ b _ h
    have h1 := litCode_pos a
    have h2 := litCode_pos b
    have h' : litCode a - 1 = litCode b - 1 := h
    exact litCode_injective (by omega)
  · intro c hc
    simp only [mem_filter, mem_range] at hc
    obtain ⟨l, hl⟩ := exists_lit hc.1
    refine ⟨l, ?_, by simp [hl]⟩
    simp [hl, hc.2]

/-! ### Digits -/

/-- The number of clause codes. -/
abbrev cap (n : ℕ) : ℕ := (2 * n + 1) ^ 3

def d0 (n k : ℕ) : ℕ := k % (2 * n + 1)
def d1 (n k : ℕ) : ℕ := k / (2 * n + 1) % (2 * n + 1)
def d2 (n k : ℕ) : ℕ := k / (2 * n + 1) / (2 * n + 1) % (2 * n + 1)

/-- The number `c` is a digit of the code `k`. -/
def InC (n c k : ℕ) : Prop := c = d0 n k ∨ c = d1 n k ∨ c = d2 n k

instance (n c k : ℕ) : Decidable (InC n c k) := by unfold InC; infer_instance

/-- The clause of a code. -/
def decode (n k : ℕ) : Finset (SignedLiteral n) := univ.filter fun l => InC n (litCode l) k

theorem mem_decode {n k : ℕ} {l : SignedLiteral n} : l ∈ decode n k ↔ InC n (litCode l) k := by
  simp [decode]

/-- A valid code: its digits are sorted, and strictly increasing where they are not zero. -/
def ValidC (n k : ℕ) : Prop := (d0 n k = 0 ∨ d0 n k < d1 n k) ∧ (d1 n k = 0 ∨ d1 n k < d2 n k)

theorem d0_lt (n k : ℕ) : d0 n k < 2 * n + 1 := Nat.mod_lt _ (by omega)
theorem d1_lt (n k : ℕ) : d1 n k < 2 * n + 1 := Nat.mod_lt _ (by omega)
theorem d2_lt (n k : ℕ) : d2 n k < 2 * n + 1 := Nat.mod_lt _ (by omega)

/-- The number with the digits `a`, `b`, `c`. -/
def mk (n a b c : ℕ) : ℕ := a + (2 * n + 1) * (b + (2 * n + 1) * c)

theorem mk_digits {n a b c : ℕ} (ha : a < 2 * n + 1) (hb : b < 2 * n + 1) (hc : c < 2 * n + 1) :
    d0 n (mk n a b c) = a ∧ d1 n (mk n a b c) = b ∧ d2 n (mk n a b c) = c := by
  have h0 : mk n a b c % (2 * n + 1) = a := by
    rw [mk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h1 : mk n a b c / (2 * n + 1) = b + (2 * n + 1) * c := by
    rw [mk, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ha, zero_add]
  have h2 : (b + (2 * n + 1) * c) % (2 * n + 1) = b := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have h3 : (b + (2 * n + 1) * c) / (2 * n + 1) = c := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
  refine ⟨h0, ?_, ?_⟩
  · rw [d1, h1, h2]
  · rw [d2, h1, h3, Nat.mod_eq_of_lt hc]

theorem mk_lt {n a b c : ℕ} (ha : a < 2 * n + 1) (hb : b < 2 * n + 1) (hc : c < 2 * n + 1) :
    mk n a b c < cap n := by
  have h1 : b + (2 * n + 1) * c < (2 * n + 1) * (2 * n + 1) := by nlinarith
  have h2 : a + (2 * n + 1) * (b + (2 * n + 1) * c) < (2 * n + 1) * ((2 * n + 1) * (2 * n + 1)) := by
    nlinarith
  calc mk n a b c < (2 * n + 1) * ((2 * n + 1) * (2 * n + 1)) := h2
    _ = cap n := by ring

theorem eq_mk {n k : ℕ} (hk : k < cap n) : k = mk n (d0 n k) (d1 n k) (d2 n k) := by
  have hG : 0 < 2 * n + 1 := by omega
  have h2 : k / (2 * n + 1) / (2 * n + 1) < 2 * n + 1 := by
    rw [Nat.div_div_eq_div_mul]
    apply Nat.div_lt_of_lt_mul
    calc k < (2 * n + 1) ^ 3 := hk
      _ = (2 * n + 1) * (2 * n + 1) * (2 * n + 1) := by ring
  have e1 := Nat.div_add_mod k (2 * n + 1)
  have e2 := Nat.div_add_mod (k / (2 * n + 1)) (2 * n + 1)
  simp only [mk, d0, d1, d2, Nat.mod_eq_of_lt h2]
  calc k = (2 * n + 1) * (k / (2 * n + 1)) + k % (2 * n + 1) := e1.symm
    _ = _ := by
      rw [add_comm]
      congr 2
      rw [add_comm] at e2
      exact e2.symm

theorem digits_unique {G x0 x1 x2 y0 y1 y2 : ℕ} (a0 : x0 < G) (a1 : x1 < G) (a2 : x2 < G)
    (b0 : y0 < G) (b1 : y1 < G) (b2 : y2 < G)
    (u1 : x0 = 0 ∨ x0 < x1) (u2 : x1 = 0 ∨ x1 < x2) (w1 : y0 = 0 ∨ y0 < y1) (w2 : y1 = 0 ∨ y1 < y2)
    (key : ∀ c, c ≠ 0 → c < G → ((c = x0 ∨ c = x1 ∨ c = x2) ↔ (c = y0 ∨ c = y1 ∨ c = y2))) :
    x0 = y0 ∧ x1 = y1 ∧ x2 = y2 := by
  have sx : (x0 = 0 ∧ x1 = 0) ∨ (x0 = 0 ∧ x1 ≠ 0 ∧ x1 < x2) ∨ (x0 ≠ 0 ∧ x0 < x1 ∧ x1 < x2) := by omega
  have sy : (y0 = 0 ∧ y1 = 0) ∨ (y0 = 0 ∧ y1 ≠ 0 ∧ y1 < y2) ∨ (y0 ≠ 0 ∧ y0 < y1 ∧ y1 < y2) := by omega
  have fx0 : x0 ≠ 0 → x0 = y0 ∨ x0 = y1 ∨ x0 = y2 := fun h => (key x0 h a0).1 (Or.inl rfl)
  have fx1 : x1 ≠ 0 → x1 = y0 ∨ x1 = y1 ∨ x1 = y2 := fun h => (key x1 h a1).1 (Or.inr (Or.inl rfl))
  have fx2 : x2 ≠ 0 → x2 = y0 ∨ x2 = y1 ∨ x2 = y2 := fun h => (key x2 h a2).1 (Or.inr (Or.inr rfl))
  have fy0 : y0 ≠ 0 → y0 = x0 ∨ y0 = x1 ∨ y0 = x2 := fun h => (key y0 h b0).2 (Or.inl rfl)
  have fy1 : y1 ≠ 0 → y1 = x0 ∨ y1 = x1 ∨ y1 = x2 := fun h => (key y1 h b1).2 (Or.inr (Or.inl rfl))
  have fy2 : y2 ≠ 0 → y2 = x0 ∨ y2 = x1 ∨ y2 = x2 := fun h => (key y2 h b2).2 (Or.inr (Or.inr rfl))
  clear key a0 a1 a2 b0 b1 b2 u1 u2 w1 w2
  rcases sx with ⟨e1, e2⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ <;>
    rcases sy with ⟨e4, e5⟩ | ⟨e4, e5, e6⟩ | ⟨e4, e5, e6⟩ <;>
    by_cases z2 : x2 = 0 <;> by_cases z2' : y2 = 0 <;>
    simp only [ne_eq, z2, z2', e1, e2, e4, e5, not_true_eq_false, IsEmpty.forall_iff,
      not_false_eq_true, forall_true_left, or_self, false_or, or_false, true_or, or_true] at fx0 fx1 fx2 fy0 fy1 fy2 <;>
    omega

/-- Two valid codes with the same clause are equal. -/
theorem valid_unique {n j k : ℕ} (hj : j < cap n) (hk : k < cap n) (vj : ValidC n j) (vk : ValidC n k)
    (h : decode n j = decode n k) : j = k := by
  have hcode : ∀ c, c ≠ 0 → c < 2 * n + 1 → (InC n c j ↔ InC n c k) := by
    intro c h0 hc
    obtain ⟨l, hl⟩ := exists_lit (n := n) (c := c - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hl
    rw [← hl, ← mem_decode, ← mem_decode, h]
  rw [eq_mk hj, eq_mk hk]
  have e := digits_unique (d0_lt n j) (d1_lt n j) (d2_lt n j) (d0_lt n k) (d1_lt n k) (d2_lt n k)
    vj.1 vj.2 vk.1 vk.2 (fun c h0 hc => hcode c h0 hc)
  rw [e.1, e.2.1, e.2.2]

/-! ### The code of a clause -/

/-- The word of a sorted list of at most three literal codes. -/
def tripleOf (n : ℕ) : List ℕ → ℕ
  | [a] => mk n 0 0 a
  | [a, b] => mk n 0 a b
  | [a, b, c] => mk n a b c
  | _ => 0

theorem tripleOf_spec {n : ℕ} (L : List ℕ) (hlen : L.length ≤ 3) (hs : L.Pairwise (· < ·))
    (hb : ∀ x ∈ L, 0 < x ∧ x < 2 * n + 1) :
    tripleOf n L < cap n ∧ ValidC n (tripleOf n L) ∧
      ∀ c, c ≠ 0 → (InC n c (tripleOf n L) ↔ c ∈ L) := by
  have h0 : 0 < 2 * n + 1 := by omega
  match L, hlen, hs, hb with
  | [], _, _, _ =>
    have := mk_digits (n := n) h0 h0 h0
    have hm : mk n 0 0 0 = 0 := by simp [mk]
    rw [hm] at this
    refine ⟨by positivity, ?_, ?_⟩
    · simp only [tripleOf, ValidC, this, true_or, and_self]
    · intro c hc
      simp only [tripleOf, InC, this]
      simp [hc]
  | [a], _, _, hb =>
    have ha := hb a (by simp)
    have := mk_digits (n := n) h0 h0 ha.2
    refine ⟨mk_lt h0 h0 ha.2, ?_, ?_⟩
    · simp only [tripleOf, ValidC, this, true_or, and_self]
    · intro c hc
      simp only [tripleOf, InC, this]
      simp [hc]
  | [a, b], _, hs, hb =>
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    have hab : a < b := by simpa using hs
    have := mk_digits (n := n) h0 ha.2 hb'.2
    refine ⟨mk_lt h0 ha.2 hb'.2, ?_, ?_⟩
    · simp only [tripleOf, ValidC, this, true_or, true_and]
      exact Or.inr hab
    · intro c hc
      simp only [tripleOf, InC, this]
      simp [hc]
  | [a, b, c], _, hs, hb =>
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    have hc' := hb c (by simp)
    have hab : a < b := by simp at hs; exact hs.1.1
    have hbc : b < c := by simp at hs; exact hs.2
    have := mk_digits (n := n) ha.2 hb'.2 hc'.2
    refine ⟨mk_lt ha.2 hb'.2 hc'.2, ?_, ?_⟩
    · simp only [tripleOf, ValidC, this]
      exact ⟨Or.inr hab, Or.inr hbc⟩
    · intro x hx
      simp only [tripleOf, InC, this]
      simp
  | _ :: _ :: _ :: _ :: _, hlen, _, _ => simp at hlen; omega

/-- The code of a clause: its sorted literal codes in base `2 * n + 1`. -/
def code (n : ℕ) (C : Finset (SignedLiteral n)) : ℕ := tripleOf n ((C.image litCode).sort (· ≤ ·))

theorem code_spec {n : ℕ} {C : Finset (SignedLiteral n)} (hC : C.card ≤ 3) :
    code n C < cap n ∧ ValidC n (code n C) ∧ decode n (code n C) = C := by
  set L := (C.image litCode).sort (· ≤ ·) with hL
  have hlen : L.length ≤ 3 := by
    rw [hL, length_sort]
    exact card_image_le.trans hC
  have hs : L.Pairwise (· < ·) := by
    have h1 : L.Pairwise (· ≤ ·) := pairwise_sort _ _
    have h2 : L.Nodup := sort_nodup _ _
    exact (h1.and h2).imp (fun ⟨h, h'⟩ => lt_of_le_of_ne h h')
  have hmem : ∀ x, x ∈ L ↔ ∃ l ∈ C, litCode l = x := by
    intro x
    rw [hL, mem_sort, mem_image]
  have hb : ∀ x ∈ L, 0 < x ∧ x < 2 * n + 1 := by
    intro x hx
    obtain ⟨l, _, rfl⟩ := (hmem x).1 hx
    have := litCode_pos l
    have := litCode_le l
    omega
  obtain ⟨h1, h2, h3⟩ := tripleOf_spec L hlen hs hb
  refine ⟨h1, h2, ?_⟩
  ext l
  rw [mem_decode]
  have := h3 (litCode l) (litCode_pos l).ne'
  change InC n (litCode l) (tripleOf n L) ↔ l ∈ C
  rw [this, hmem]
  constructor
  · rintro ⟨m, hm, he⟩
    rwa [← litCode_injective he]
  · intro h
    exact ⟨l, h, rfl⟩

theorem code_decode {n k : ℕ} (hk : k < cap n) (vk : ValidC n k)
    (hc : (decode n k).card ≤ 3) : code n (decode n k) = k := by
  obtain ⟨h1, h2, h3⟩ := code_spec hc
  exact valid_unique h1 hk h2 vk h3

/-- A clause of a code has at most three literals. -/
theorem card_decode_le (n k : ℕ) : (decode n k).card ≤ 3 := by
  classical
  have hs : (decode n k).image litCode ⊆ ({d0 n k, d1 n k, d2 n k} : Finset ℕ) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
    have := mem_decode.mp hl
    simpa [InC] using this
  have h1 : ((decode n k).image litCode).card = (decode n k).card :=
    card_image_of_injective _ litCode_injective
  have h2 := card_le_card hs
  have h3 : ({d0 n k, d1 n k, d2 n k} : Finset ℕ).card ≤ 3 := card_le_three
  omega

/-! ### Words of bits -/

/-- The word whose bit `k < N` is the indicator of `p k`. -/
noncomputable def setWord (N : ℕ) (p : ℕ → Prop) : ℕ := ∑ k ∈ range N, 2 ^ k * ind (p k)

theorem setWord_lt (N : ℕ) (p : ℕ → Prop) : setWord N p < 2 ^ N := by
  induction N with
  | zero => simp [setWord]
  | succ N ih =>
    have h : setWord (N + 1) p = setWord N p + 2 ^ N * ind (p N) := by
      simp [setWord, sum_range_succ]
    have h1 := ind_le_one (p N)
    have h2 : 2 ^ N * ind (p N) ≤ 2 ^ N * 1 := Nat.mul_le_mul_left _ h1
    rw [h, pow_succ]
    omega

theorem setWord_testBit (N : ℕ) (p : ℕ → Prop) (i : ℕ) :
    (setWord N p).testBit i = true ↔ i < N ∧ p i := by
  induction N with
  | zero => simp [setWord]
  | succ N ih =>
    have h : setWord (N + 1) p = 2 ^ N * ind (p N) + setWord N p := by
      simp [setWord, sum_range_succ, add_comm]
    rw [h, Nat.testBit_two_pow_mul_add _ (setWord_lt N p)]
    split
    · rw [ih]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨_, h2⟩
        exact ⟨by assumption, h2⟩
    · rename_i hi
      by_cases hN : i = N
      · subst hN
        by_cases hp : p i <;> simp [ind, hp]
      · have hi' : ¬ i < N + 1 := by omega
        have : ind (p N) ≤ 1 := ind_le_one _
        have h0 : (ind (p N)).testBit (i - N) = false := by
          have hpos : 0 < i - N := by omega
          obtain ⟨m, hm⟩ : ∃ m, i - N = m + 1 := ⟨i - N - 1, by omega⟩
          rw [hm, Nat.testBit_succ]
          have : ind (p N) / 2 = 0 := by omega
          simp [this]
        rw [h0]
        simp [hi']

/-! ### The word of a formula -/

/-- The word of a formula. -/
noncomputable def encF (n : ℕ) (F : ClauseSet (SignedLiteral n)) : ℕ := ∑ C ∈ F, 2 ^ code n C

/-- The code `k` is the code of a clause of `F`. -/
def Cl (n : ℕ) (F : ClauseSet (SignedLiteral n)) (k : ℕ) : Prop := ValidC n k ∧ decode n k ∈ F

/-- Formula width. -/
def Wide3 {n : ℕ} (F : ClauseSet (SignedLiteral n)) : Prop := ∀ C ∈ F, C.card ≤ 3

open Classical in
theorem sum_clause {n : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) (f : ℕ → ℕ) :
    ∑ C ∈ F, f (code n C) = ∑ k ∈ (range (cap n)).filter (Cl n F), f k := by
  apply Finset.sum_nbij' (code n) (decode n)
  · intro C hC
    obtain ⟨h1, h2, h3⟩ := code_spec (hF C hC)
    simp only [mem_filter, mem_range]
    exact ⟨h1, h2, by rwa [h3]⟩
  · intro k hk
    exact (mem_filter.mp hk).2.2
  · intro C hC
    exact (code_spec (hF C hC)).2.2
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    exact code_decode hk.1 hk.2.1 (card_decode_le n k)
  · intro _ _
    rfl

theorem encF_eq_setWord {n : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) :
    encF n F = setWord (cap n) (Cl n F) := by
  classical
  rw [encF, sum_clause hF (fun k => 2 ^ k), setWord, sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases h : Cl n F k <;> simp [h, ind]

theorem encF_lt {n : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) : encF n F < 2 ^ cap n := by
  rw [encF_eq_setWord hF]
  exact setWord_lt _ _

/-- A bit of the word of a formula. -/
theorem encF_testBit {n : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {k : ℕ} (hk : k < cap n) :
    (encF n F).testBit k = true ↔ Cl n F k := by
  rw [encF_eq_setWord hF, setWord_testBit]
  simp [hk]

/-- A word built from a predicate that agrees with `Cl` is the word of the formula. -/
theorem setWord_eq_encF {n : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {p : ℕ → Prop}
    (h : ∀ k < cap n, p k ↔ Cl n F k) : setWord (cap n) p = encF n F := by
  rw [encF_eq_setWord hF]
  unfold setWord
  apply sum_congr rfl
  intro k hk
  rw [ind_congr (h k (mem_range.mp hk))]

theorem exists_clause {n : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F)
    (P : Finset (SignedLiteral n) → Prop) :
    (∃ D ∈ F, P D) ↔ ∃ j < cap n, Cl n F j ∧ P (decode n j) := by
  constructor
  · rintro ⟨D, hD, hP⟩
    obtain ⟨h1, h2, h3⟩ := code_spec (hF D hD)
    exact ⟨code n D, h1, ⟨h2, by rwa [h3]⟩, by rwa [h3]⟩
  · rintro ⟨j, _, ⟨_, h2⟩, h3⟩
    exact ⟨_, h2, h3⟩

open Classical in
theorem card_filter_clause {n : ℕ} {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F)
    (P : Finset (SignedLiteral n) → Prop) :
    (F.filter P).card = ∑ k ∈ range (cap n), ind (Cl n F k ∧ P (decode n k)) := by
  have hF' : Wide3 (F.filter P) := fun C hC => hF C (mem_filter.mp hC).1
  have h1 := sum_clause hF' (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one] at h1
  rw [h1, card_filter]
  apply sum_congr rfl
  intro k _
  by_cases h : Cl n F k ∧ P (decode n k)
  · rw [ind_pos h, if_pos]
    exact ⟨h.1.1, mem_filter.mpr ⟨h.1.2, h.2⟩⟩
  · rw [ind_neg h, if_neg]
    rintro ⟨h1, h2⟩
    exact h ⟨⟨h1, (mem_filter.mp h2).1⟩, (mem_filter.mp h2).2⟩

/-! ### Clause tests in terms of literal codes -/

theorem decode_subset_iff {n j k : ℕ} :
    decode n j ⊆ decode n k ↔ ∀ c < 2 * n, InC n (c + 1) j → InC n (c + 1) k := by
  have := forall_lit_iff (n := n) (fun x => InC n x j → InC n x k)
  rw [← this]
  simp only [Finset.subset_iff, mem_decode]

theorem card_decode (n k : ℕ) : (decode n k).card = ∑ c ∈ range (2 * n), ind (InC n (c + 1) k) := by
  classical
  rw [show ∑ c ∈ range (2 * n), ind (InC n (c + 1) k) = _ from
    (card_filter_lit (n := n) (fun x => InC n x k)).symm]
  congr 1
  ext l
  simp [mem_decode]

theorem tautological_decode {n k : ℕ} :
    tautological (decode n k) ↔ ∃ v < n, InC n (2 * v + 1) k ∧ InC n (2 * v + 2) k := by
  simp only [tautological, mem_decode, litCode]
  constructor
  · rintro ⟨v, h1, h2⟩
    exact ⟨v, v.2, by simpa using h1, by simpa using h2⟩
  · rintro ⟨v, hv, h1, h2⟩
    exact ⟨⟨v, hv⟩, by simpa using h1, by simpa using h2⟩

end TransposeBase.Pseudo.CnfTree
