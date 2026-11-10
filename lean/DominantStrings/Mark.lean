import DominantStrings.Seed

/-!
# Difference marks

A bundle of `w` wires has the tail ends `t` and the head ends `h`, as numbers of `w` bits, and the marks
`mkW w t h = ∏ j, (h_j - t_j)` (`Seed`). This file collects what the proof of one level needs:

* `mk_eq`: the marks vanish unless `h` is the complement `compN w t`, and then they are the sign `sgnP w t`;
* `mk_swap`, `mk_split`, `mk_viewL`: reversing a bundle, and splitting it into parts;
* `sum_mk_index`, `sum_mk_tests`: the sums over the two ends of a bundle that carries an index or a copy;
* `sum_pair_viewL`, `sum_pair_prod`: sums over the ends of all bundles, as products;
* `prod_sym_order`: a product over the pairs `x < y` of a symmetric function does not depend on the order.
-/

namespace DominantStrings

open Finset

/-- The sign of `d` tail ends: `(-1)` to the number of ones of `t` below `d`. -/
def sgnP (d t : ℕ) : ℤ := ∏ j ∈ range d, (if t.testBit j then -1 else 1)

/-- The complement of a number of `d` bits. -/
def compN (d t : ℕ) : ℕ := 2 ^ d - 1 - t

theorem mk_zero (t h : ℕ) : mkW 0 t h = 1 := by simp [mkW]

/-- Reversing a bundle of `w` wires. -/
theorem mk_swap (w t h : ℕ) : mkW w h t = (-1) ^ w * mkW w t h := by
  unfold mkW
  rw [show ((-1 : ℤ)) ^ w = ∏ _j ∈ range w, (-1 : ℤ) by simp, ← prod_mul_distrib]
  exact prod_congr rfl fun j _ => by ring

theorem compN_lt (d t : ℕ) : compN d t < 2 ^ d := by
  have := Nat.one_le_two_pow (n := d)
  unfold compN
  omega

theorem compN_compN {d t : ℕ} (ht : t < 2 ^ d) : compN d (compN d t) = t := by
  have := Nat.one_le_two_pow (n := d)
  unfold compN
  omega

theorem testBit_compN {d t j : ℕ} (ht : t < 2 ^ d) (hj : j < d) : (compN d t).testBit j = !t.testBit j :=
  testBit_comp ht hj

theorem sgnP_mul_self (d t : ℕ) : sgnP d t * sgnP d t = 1 := by
  unfold sgnP
  rw [← prod_mul_distrib]
  exact prod_eq_one fun j _ => by split_ifs <;> norm_num

/-- The marks of a bundle are its sign when the head ends are the complement, and `0` otherwise. -/
theorem mk_eq {d t h : ℕ} (ht : t < 2 ^ d) (hh : h < 2 ^ d) :
    mkW d t h = if h = compN d t then sgnP d t else 0 := by
  by_cases e : h = compN d t
  · subst e
    rw [if_pos rfl]
    unfold mkW sgnP
    refine prod_congr rfl fun j hj => ?_
    rw [testBit_compN ht (mem_range.1 hj)]
    cases t.testBit j <;> simp [b2z]
  · rw [if_neg e]
    have hex : ∃ j < d, h.testBit j = t.testBit j := by
      by_contra hc
      push_neg at hc
      apply e
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < d
      · rw [testBit_compN ht hj]
        have := hc j hj
        cases hh' : h.testBit j <;> cases ht' : t.testBit j <;> simp_all
      · have hle : 2 ^ d ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hj)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hh hle),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (compN_lt d t) hle)]
    obtain ⟨j, hj, hb⟩ := hex
    exact prod_eq_zero (mem_range.2 hj) (by rw [hb]; ring)

/-- A bundle that carries an index: the tail side has the sign of the index, and the head side reads the complement. -/
theorem sum_mk_index (d : ℕ) (A B : ℕ → ℤ) :
    ∑ y ∈ range (2 ^ d), ∑ y' ∈ range (2 ^ d), mkW d y y' * (sgnP d y * A y) * B (compN d y') =
      ∑ y ∈ range (2 ^ d), A y * B y := by
  refine sum_congr rfl fun y hy => ?_
  have hy' := mem_range.1 hy
  have h1 : ∀ y' ∈ range (2 ^ d), mkW d y y' * (sgnP d y * A y) * B (compN d y') =
      if y' = compN d y then sgnP d y * (sgnP d y * A y) * B (compN d y') else 0 := by
    intro y' hy2
    rw [mk_eq hy' (mem_range.1 hy2)]
    split_ifs <;> simp
  rw [sum_congr rfl h1, sum_ite_eq', if_pos (mem_range.2 (compN_lt d y)), compN_compN hy',
    ← mul_assoc, sgnP_mul_self, one_mul]

/-- A bundle that carries a copy: each end is tested against one number. -/
theorem sum_mk_tests {c α β : ℕ} (hα : α < 2 ^ c) (hβ : β < 2 ^ c) (X Y : ℤ) :
    ∑ a ∈ range (2 ^ c), ∑ a' ∈ range (2 ^ c),
        mkW c a a' * ((if a = α then 1 else 0) * X) * ((if a' = β then 1 else 0) * Y) =
      mkW c α β * X * Y := by
  have h1 : ∀ a ∈ range (2 ^ c), ∑ a' ∈ range (2 ^ c),
      mkW c a a' * ((if a = α then 1 else 0) * X) * ((if a' = β then 1 else 0) * Y) =
      mkW c a β * ((if a = α then 1 else 0) * X) * Y := by
    intro a _
    have h2 : ∀ a' ∈ range (2 ^ c), mkW c a a' * ((if a = α then 1 else 0) * X) * ((if a' = β then 1 else 0) * Y) =
        if a' = β then mkW c a a' * ((if a = α then 1 else 0) * X) * Y else 0 := by
      intro a' _
      split_ifs <;> simp
    rw [sum_congr rfl h2, sum_ite_eq', if_pos (mem_range.2 hβ)]
  rw [sum_congr rfl h1]
  have h3 : ∀ a ∈ range (2 ^ c), mkW c a β * ((if a = α then 1 else 0) * X) * Y =
      if a = α then mkW c a β * X * Y else 0 := by
    intro a _
    split_ifs <;> simp
  rw [sum_congr rfl h3, sum_ite_eq', if_pos (mem_range.2 hα)]

theorem testBit_field (Z o k i : ℕ) (hi : i < k) : (Z / 2 ^ o % 2 ^ k).testBit i = Z.testBit (o + i) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hi, Nat.add_comm]

/-- A bundle splits into its low `p` wires and the rest. -/
theorem mk_split {p w : ℕ} (hp : p ≤ w) (t h : ℕ) :
    mkW w t h = mkW p (t % 2 ^ p) (h % 2 ^ p) * mkW (w - p) (t / 2 ^ p) (h / 2 ^ p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [Nat.add_sub_cancel_left]
  unfold mkW
  rw [prod_range_add]
  congr 1
  · refine prod_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    simp [hj']
  · refine prod_congr rfl fun j _ => ?_
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.add_comm j p]

/-- A bundle splits into the fields of `viewL`. -/
theorem mk_viewL (n : ℕ) (a : ℕ → ℕ) (b b' : ℕ) :
    mkW (∑ t ∈ range n, a t) b b' = ∏ t ∈ range n, mkW (a t) (viewL n a b t) (viewL n a b' t) := by
  induction n with
  | zero => simp [mkW]
  | succ n ih =>
    rw [sum_range_succ, prod_range_succ]
    have hv : ∀ t ∈ range n, mkW (a t) (viewL (n + 1) a b t) (viewL (n + 1) a b' t) =
        mkW (a t) (viewL n a b t) (viewL n a b' t) := by
      intro t ht
      have ht' := mem_range.1 ht
      simp only [viewL, ht', Nat.lt_succ_of_lt ht', if_true]
    rw [prod_congr rfl hv, ← ih]
    unfold mkW
    rw [prod_range_add]
    congr 1
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    simp only [viewL, Nat.lt_succ_self, if_true]
    rw [testBit_field _ _ _ _ hi', testBit_field _ _ _ _ hi']

/-- A sum over two numbers of a product over their fields. -/
theorem sum_pair_viewL {β : Type*} [CommRing β] (n : ℕ) (a : ℕ → ℕ) (g : ℕ → ℕ → ℕ → β) :
    ∑ b ∈ range (2 ^ ∑ t ∈ range n, a t), ∑ b' ∈ range (2 ^ ∑ t ∈ range n, a t),
        ∏ t ∈ range n, g t (viewL n a b t) (viewL n a b' t) =
      ∏ t ∈ range n, ∑ x ∈ range (2 ^ a t), ∑ x' ∈ range (2 ^ a t), g t x x' := by
  have h1 : ∀ b, ∑ b' ∈ range (2 ^ ∑ t ∈ range n, a t), ∏ t ∈ range n, g t (viewL n a b t) (viewL n a b' t) =
      ∏ t ∈ range n, ∑ x' ∈ range (2 ^ a t), g t (viewL n a b t) x' :=
    fun b => prod_sum_viewL n a (fun t x' => g t (viewL n a b t) x')
  simp only [h1]
  exact prod_sum_viewL n a (fun t x => ∑ x' ∈ range (2 ^ a t), g t x x')

/-- A sum over the families of numbers on the ordered pairs, of a product over the pairs `u < u'` of a function of the
two numbers of the pair, is a product of sums. -/
theorem sum_pair_prod {β : Type*} [CommRing β] (n : ℕ) (w : ℕ → ℕ → ℕ) (hsym : ∀ x y, w x y = w y x)
    (h0 : ∀ x, w x x = 0) (Φ : ℕ → ℕ → ℕ → ℕ → β) :
    ∑ B ∈ cube n (fun x => cube n (fun y => range (2 ^ w x y))),
        ∏ u ∈ range n, ∏ u' ∈ range n, (if u < u' then Φ u u' (B u u') (B u' u) else 1) =
      ∏ u ∈ range n, ∏ u' ∈ range n,
        (if u < u' then ∑ b ∈ range (2 ^ w u u'), ∑ b' ∈ range (2 ^ w u u'), Φ u u' b b' else 1) := by
  classical
  set S : ℕ → ℕ → Finset (ℕ × ℕ) := fun u u' =>
    if u < u' then range (2 ^ w u u') ×ˢ range (2 ^ w u u') else {0} with hS
  set H : ℕ → ℕ → ℕ × ℕ → β := fun u u' p => if u < u' then Φ u u' p.1 p.2 else 1 with hH
  have hR : ∏ u ∈ range n, ∏ u' ∈ range n,
        (if u < u' then ∑ b ∈ range (2 ^ w u u'), ∑ b' ∈ range (2 ^ w u u'), Φ u u' b b' else 1) =
      ∑ P ∈ cube n (fun u => cube n (S u)), ∏ u ∈ range n, ∏ u' ∈ range n, H u u' (P u u') := by
    rw [sum_cube_prod n (fun u => cube n (S u)) (fun u f => ∏ u' ∈ range n, H u u' (f u'))]
    refine prod_congr rfl fun u _ => ?_
    rw [sum_cube_prod n (S u) (H u)]
    refine prod_congr rfl fun u' _ => ?_
    by_cases huu : u < u'
    · simp only [hS, hH, huu, if_true]
      rw [sum_product]
    · simp [hS, hH, huu]
  rw [hR]
  refine sum_nbij' (fun B u u' => if u < u' then (B u u', B u' u) else 0)
    (fun P u u' => if u < u' then (P u u').1 else if u' < u then (P u' u).2 else 0) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    rw [mem_cube] at hB
    obtain ⟨hB1, hB2⟩ := hB
    rw [mem_cube]
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [mem_cube]
      refine ⟨fun u' hu' => ?_, fun u' hu' => ?_⟩
      · by_cases huu : u < u'
        · have e1 := (mem_cube.1 (hB1 u hu)).1 u' hu'
          have e2 := (mem_cube.1 (hB1 u' hu')).1 u hu
          rw [hsym u' u] at e2
          simp only [hS, huu, if_true, mem_product]
          exact ⟨e1, e2⟩
        · simp [hS, huu]
      · have e1 : B u u' = 0 := (mem_cube.1 (hB1 u hu)).2 u' hu'
        have e2 : B u' = 0 := hB2 u' hu'
        have huu : u < u' := by omega
        simp [huu, e1, e2]
    · funext u'
      have e1 : B u u' = 0 := by rw [hB2 u hu]; rfl
      have e2 : B u' u = 0 := by
        by_cases hu' : u' < n
        · exact (mem_cube.1 (hB1 u' hu')).2 u hu
        · rw [hB2 u' (by omega)]; rfl
      by_cases huu : u < u' <;> simp [huu, e1, e2]
  · intro P hP
    rw [mem_cube] at hP
    obtain ⟨hP1, hP2⟩ := hP
    rw [mem_cube]
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [mem_cube]
      refine ⟨fun u' hu' => ?_, fun u' hu' => ?_⟩
      · rcases lt_trichotomy u u' with h | rfl | h
        · have := (mem_cube.1 (hP1 u hu)).1 u' hu'
          simp only [hS, h, if_true, mem_product] at this
          simpa [h] using this.1
        · simp [h0]
        · have := (mem_cube.1 (hP1 u' hu')).1 u hu
          simp only [hS, h, if_true, mem_product] at this
          have h' : ¬ u < u' := by omega
          simpa [h', h, hsym u u'] using this.2
      · have e : P u u' = 0 := (mem_cube.1 (hP1 u hu)).2 u' hu'
        have huu : u < u' := by omega
        simp [huu, e]
    · funext u'
      have e1 : P u u' = 0 := by rw [hP2 u hu]; rfl
      have e2 : P u' u = 0 := by
        by_cases hu' : u' < n
        · exact (mem_cube.1 (hP1 u' hu')).2 u hu
        · rw [hP2 u' (by omega)]; rfl
      by_cases h1 : u < u' <;> by_cases h2 : u' < u <;> simp [h1, h2, e1, e2]
  · intro B hB
    rw [mem_cube] at hB
    obtain ⟨hB1, hB2⟩ := hB
    funext u u'
    rcases lt_trichotomy u u' with h | rfl | h
    · simp [h]
    · have hz : B u u = 0 := by
        by_cases hu : u < n
        · have := (mem_cube.1 (hB1 u hu)).1 u hu
          rw [h0, pow_zero, range_one, mem_singleton] at this
          exact this
        · rw [hB2 u (by omega)]
          rfl
      simp [hz]
    · have h' : ¬ u < u' := by omega
      simp [h', h]
  · intro P hP
    rw [mem_cube] at hP
    obtain ⟨hP1, hP2⟩ := hP
    funext u u'
    by_cases h : u < u'
    · have h' : ¬ u' < u := by omega
      simp [h, h']
    · have hz : P u u' = 0 := by
        by_cases hu : u < n
        · by_cases hu' : u' < n
          · have := (mem_cube.1 (hP1 u hu)).1 u' hu'
            simp only [hS, h, if_false, mem_singleton] at this
            exact this
          · exact (mem_cube.1 (hP1 u hu)).2 u' (by omega)
        · rw [hP2 u (by omega)]
          rfl
      simp [h, hz]
  · intro B _
    refine prod_congr rfl fun u _ => prod_congr rfl fun u' _ => ?_
    by_cases h : u < u'
    · simp [hH, h]
    · simp [hH, h]

/-- A product over the pairs `x < y` of a symmetric function is the product over the pairs `σ x < σ y`, for a map `σ`
that is injective below `N`. -/
theorem prod_sym_order {β : Type*} [CommMonoid β] (N : ℕ) (σ : ℕ → ℕ) (hσ : Set.InjOn σ (range N : Set ℕ))
    (f : ℕ → ℕ → β) (hf : ∀ x y, f x y = f y x) :
    ∏ x ∈ range N, ∏ y ∈ range N, (if x < y then f x y else 1) =
      ∏ x ∈ range N, ∏ y ∈ range N, (if σ x < σ y then f x y else 1) := by
  have h1 : ∀ x y, (if σ x < σ y then f x y else 1) =
      (if σ x < σ y ∧ x < y then f x y else 1) * (if σ x < σ y ∧ y < x then f x y else 1) := by
    intro x y
    by_cases hs : σ x < σ y
    · have hne : x ≠ y := fun e => by rw [e] at hs; exact lt_irrefl _ hs
      rcases lt_or_gt_of_ne hne with h | h
      · simp [hs, h, not_lt.2 h.le]
      · simp [hs, h, not_lt.2 h.le]
    · simp [hs]
  simp only [h1, prod_mul_distrib]
  have h2 : ∏ x ∈ range N, ∏ y ∈ range N, (if σ x < σ y ∧ y < x then f x y else 1) =
      ∏ x ∈ range N, ∏ y ∈ range N, (if σ y < σ x ∧ x < y then f x y else 1) := by
    rw [prod_comm]
    refine prod_congr rfl fun x _ => prod_congr rfl fun y _ => ?_
    rw [hf]
  rw [h2, ← prod_mul_distrib]
  refine prod_congr rfl fun x hx => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun y hy => ?_
  by_cases h : x < y
  · have hne : σ x ≠ σ y := fun e => h.ne (hσ (mem_coe.2 hx) (mem_coe.2 hy) e)
    rcases lt_or_gt_of_ne hne with hs | hs
    · simp [h, hs, not_lt.2 hs.le]
    · simp [h, hs, not_lt.2 hs.le]
  · simp [h]

end DominantStrings
