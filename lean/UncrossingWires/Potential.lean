import UncrossingWires.Step

/-!
# The potential

`psi K w` is the sum of the squares of the weights. The number `K ^ 2 * psi K w` is the square of the
potential of the paper. One of the two directions makes it smaller by the factor `24 / 25` (`potential_min`).

The proof of `potential_two` compares the two directions on each quadruple `(a, a', b, b')` of coordinates of rows and
columns. `Pot.GG l u u' v v'` holds the new wires of the two segments `(v, v')` and `(v', v)` of the pair `u, u'`, and
`Pot.quad_all` is the inequality for one quadruple. It does not need any order of the coordinates, so the sum over all
quadruples runs without a case split.
-/

namespace UncrossingWires

open Finset

/-- The sum of the squares of the weights. -/
def psi (K : ℕ) (w : ℕ → ℕ → ℕ) : ℕ := ∑ x ∈ range K, ∑ y ∈ range K, w x y ^ 2

/-- The weights of the two directions, for one code. -/
def rowW (K' : ℕ) (w : ℕ → ℕ → ℕ) (c scale : ℕ) : ℕ → ℕ → ℕ := Lev.newW ⟨K', w, c, true, scale⟩

def colW (K' : ℕ) (w : ℕ → ℕ → ℕ) (c scale : ℕ) : ℕ → ℕ → ℕ := Lev.newW ⟨K', w, c, false, scale⟩

/-- The direction with the smaller sum of squares. -/
def dirOf (K' : ℕ) (w : ℕ → ℕ → ℕ) (scale c : ℕ) : Bool :=
  decide (psi K' (rowW K' w c scale) ≤ psi K' (colW K' w c scale))

namespace Pot

/-! ### Reindexing by digits -/

/-- A sum over `range (n * K)` is a sum over the digits of `a * K + b`. -/
theorem sum_range_mul_digits {β : Type*} [AddCommMonoid β] (n K : ℕ) (f : ℕ → β) :
    ∑ x ∈ range (n * K), f x = ∑ a ∈ range n, ∑ b ∈ range K, f (a * K + b) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- A function of the digits `s / K` and `s % K` of `s < K * K`. -/
theorem sum_digits {β : Type*} [AddCommMonoid β] (K : ℕ) (F : ℕ → ℕ → β) :
    ∑ s ∈ range (K * K), F (s / K) (s % K) = ∑ v ∈ range K, ∑ v' ∈ range K, F v v' := by
  rw [sum_range_mul_digits]
  refine sum_congr rfl fun v _ => sum_congr rfl fun v' hv' => ?_
  have hv'' := mem_range.mp hv'
  have hK : 0 < K := by omega
  congr 1
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hv'', zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv'']

/-- The map `wd` is a bijection from pairs of coordinates onto the words, for each direction. -/
theorem sum_wd {β : Type*} [AddCommMonoid β] (l : Lev) (f : ℕ → β) :
    ∑ u ∈ range l.K', ∑ v ∈ range l.K', f (l.wd u v) = ∑ x ∈ range (l.K' * l.K'), f x := by
  rw [sum_range_mul_digits]
  simp only [Lev.wd]
  cases l.dir
  · simp only [Bool.false_eq_true, if_false]
    exact sum_comm
  · simp only [if_true]

/-- The sum of squares, in the coordinates of rows and columns. -/
theorem psi_digits (K' : ℕ) (w : ℕ → ℕ → ℕ) :
    psi (K' * K') w = ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
      w (a * K' + b) (a' * K' + b') ^ 2 := by
  unfold psi
  rw [sum_range_mul_digits]
  refine sum_congr rfl fun a _ => ?_
  calc _ = ∑ b ∈ range K', ∑ a' ∈ range K', ∑ b' ∈ range K', w (a * K' + b) (a' * K' + b') ^ 2 :=
        sum_congr rfl fun b _ => sum_range_mul_digits K' K' _
    _ = _ := sum_comm

/-- One sum moves past two sums. -/
theorem sum3_comm {β : Type*} [AddCommMonoid β] (s t : Finset ℕ) (Z : ℕ → ℕ → ℕ → β) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ b' ∈ t, Z a b b' = ∑ b ∈ t, ∑ b' ∈ t, ∑ a ∈ s, Z a b b' := by
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_comm

/-- The order of four sums over two sets. -/
theorem sum4_swap {β : Type*} [AddCommMonoid β] (s t : Finset ℕ) (X : ℕ → ℕ → ℕ → ℕ → β) :
    ∑ a ∈ s, ∑ a' ∈ s, ∑ b ∈ t, ∑ b' ∈ t, X a a' b b' =
      ∑ b ∈ t, ∑ b' ∈ t, ∑ a ∈ s, ∑ a' ∈ s, X a a' b b' := by
  rw [← sum3_comm s t (fun a b b' => ∑ a' ∈ s, X a a' b b')]
  exact sum_congr rfl fun a _ => sum3_comm s t _

/-- Cauchy for a double sum. -/
theorem sq_sum_sum_le (s t : Finset ℕ) (f : ℕ → ℕ → ℕ) :
    (∑ i ∈ s, ∑ j ∈ t, f i j) ^ 2 ≤ #s * #t * ∑ i ∈ s, ∑ j ∈ t, f i j ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := s ×ˢ t) (f := fun p => f p.1 p.2)
  rw [card_product, sum_product, sum_product] at this
  simpa using this

/-! ### The new wires of a pair of segments -/

/-- The new wires of the two segments `(v, v')` and `(v', v)` of a pair `u < u'`. -/
def gg (l : Lev) (u u' v v' : ℕ) : ℕ := l.seg u u' v v' + l.seg u u' v' v

/-- The new wires of the two segments, for any order of `u` and `u'`. It is zero for `u = u'`. -/
def GG (l : Lev) (u u' v v' : ℕ) : ℕ :=
  if u = u' then 0 else gg l (min u u') (max u u') v v'

theorem newW_eq_sum (l : Lev) {u u' : ℕ} (h : u ≠ u') :
    l.newW u u' = ∑ v ∈ range l.K', ∑ v' ∈ range l.K', l.seg (min u u') (max u u') v v' := by
  rw [Lev.newW, if_neg h]
  exact sum_digits l.K' _

/-- Twice the new weight is the sum of `GG`. -/
theorem two_newW (l : Lev) {u u' : ℕ} (h : u ≠ u') :
    2 * l.newW u u' = ∑ v ∈ range l.K', ∑ v' ∈ range l.K', GG l u u' v v' := by
  rw [newW_eq_sum l h]
  simp only [GG, if_neg h, gg, sum_add_distrib]
  rw [two_mul]
  congr 1
  exact sum_comm

theorem four_newW_sq_le (l : Lev) (u u' : ℕ) :
    4 * l.newW u u' ^ 2 ≤ l.K' ^ 2 * ∑ v ∈ range l.K', ∑ v' ∈ range l.K', GG l u u' v v' ^ 2 := by
  by_cases h : u = u'
  · subst h
    simp [Lev.newW]
  · have h2 := two_newW l h
    have h3 := sq_sum_sum_le (range l.K') (range l.K') (GG l u u')
    rw [← h2] at h3
    simp only [card_range] at h3
    calc 4 * l.newW u u' ^ 2 = (2 * l.newW u u') ^ 2 := by ring
      _ ≤ _ := h3
      _ = _ := by ring

/-- Cauchy on each pair `u, u'`. -/
theorem four_psi_le (l : Lev) :
    4 * psi l.K' l.newW ≤ l.K' ^ 2 * ∑ u ∈ range l.K', ∑ u' ∈ range l.K',
      ∑ v ∈ range l.K', ∑ v' ∈ range l.K', GG l u u' v v' ^ 2 := by
  unfold psi
  simp only [mul_sum (a := 4), mul_sum (a := l.K' ^ 2)]
  refine sum_le_sum fun u _ => sum_le_sum fun u' _ => ?_
  simpa only [mul_sum] using four_newW_sq_le l u u'

theorem GG_comm_v (l : Lev) (u u' v v' : ℕ) : GG l u u' v v' = GG l u u' v' v := by
  simp only [GG, gg, add_comm]

theorem GG_comm_u (l : Lev) (u u' v v' : ℕ) : GG l u u' v v' = GG l u' u v v' := by
  simp only [GG, min_comm u u', max_comm u u', eq_comm]

theorem seg_same (l : Lev) (u u' v : ℕ) : l.seg u u' v v = l.w (l.wd u v) (l.wd u' v) := by
  simp [Lev.seg, Lev.carry, Lev.dd, Lev.pm]

/-- The two segments of a rectangle. -/
theorem gg_of_lt (l : Lev) {u u' v v' : ℕ} (hu : u ≠ u') (hv : v < v') :
    gg l u u' v v' =
      (l.w (l.wd u v) (l.wd u' v') - oddMin (l.w (l.wd u v) (l.wd u' v')) (l.w (l.wd u v') (l.wd u' v))) +
        dLen (l.pol u u' v v' == l.dir)
          (oddMin (l.w (l.wd u v) (l.wd u' v')) (l.w (l.wd u v') (l.wd u' v))) +
        (l.w (l.wd u v') (l.wd u' v) - oddMin (l.w (l.wd u v) (l.wd u' v')) (l.w (l.wd u v') (l.wd u' v))) := by
  have h1 : v ≠ v' := hv.ne
  have h2 : ¬ v' < v := by omega
  simp only [gg, Lev.seg, Lev.carry, Lev.dd, Lev.pm, hu, h1, h1.symm, false_or, if_false, if_pos hv, if_neg h2,
    add_zero]
  rw [oddMin_comm (l.w (l.wd u v') (l.wd u' v))]

/-- The sum of the squares of the two widths of a rectangle. -/
theorem sq_two_widths (w1 w2 f : ℕ) (h : 10 * f ≤ 10 * max w1 w2 + 9 * min w1 w2) :
    25 * ((w1 + w2) ^ 2 + f ^ 2) ≤ 96 * (w1 ^ 2 + w2 ^ 2) := by
  wlog hw : w2 ≤ w1 generalizing w1 w2 with H
  · have := H w2 w1 (by rwa [max_comm, min_comm]) (by omega)
    nlinarith
  rw [max_eq_left hw, min_eq_right hw] at h
  have h2 : (10 * f) ^ 2 ≤ (10 * w1 + 9 * w2) ^ 2 := Nat.pow_le_pow_left h 2
  zify at h2 ⊢
  nlinarith [sq_nonneg (92 * (w1 : ℤ) - 95 * w2)]

/-! ### One quadruple of coordinates -/

section Two

variable (K' : ℕ) (w : ℕ → ℕ → ℕ) (c scale : ℕ)

/-- The inequality on one quadruple of coordinates of rows and columns. -/
def QuadIneq (a a' b b' : ℕ) : Prop :=
  25 * (GG ⟨K', w, c, true, scale⟩ a a' b b' ^ 2 + GG ⟨K', w, c, false, scale⟩ b b' a a' ^ 2) ≤
    96 * (w (a * K' + b) (a' * K' + b') ^ 2 + w (a * K' + b') (a' * K' + b) ^ 2)

variable {K' w c scale}

theorem QuadIneq.swap_a (hsym : ∀ x y, w x y = w y x) {a a' b b' : ℕ} (h : QuadIneq K' w c scale a' a b b') :
    QuadIneq K' w c scale a a' b b' := by
  unfold QuadIneq at h ⊢
  rw [GG_comm_u _ a a', GG_comm_v _ b b' a a', hsym (a * K' + b), hsym (a * K' + b'), add_comm (_ ^ 2)
    (w (a' * K' + b) _ ^ 2)]
  exact h

theorem QuadIneq.swap_b {a a' b b' : ℕ} (h : QuadIneq K' w c scale a a' b' b) :
    QuadIneq K' w c scale a a' b b' := by
  unfold QuadIneq at h ⊢
  rw [GG_comm_v _ a a' b b', GG_comm_u _ b b' a a', add_comm (w (a * K' + b) _ ^ 2)]
  exact h

/-- A rectangle: `pol` reads the same bit in the two directions, so one of the two widths is the short one. -/
theorem quad_rect (hsym : ∀ x y, w x y = w y x) {a a' b b' : ℕ} (ha : a < a') (hb : b < b') :
    QuadIneq K' w c scale a a' b b' := by
  unfold QuadIneq
  have hr : ∀ l : Lev, GG l a a' b b' = gg l a a' b b' := fun l => by
    simp [GG, ha.ne, min_eq_left ha.le, max_eq_right ha.le]
  have hc : ∀ l : Lev, GG l b b' a a' = gg l b b' a a' := fun l => by
    simp [GG, hb.ne, min_eq_left hb.le, max_eq_right hb.le]
  rw [hr, hc, gg_of_lt _ ha.ne hb, gg_of_lt _ hb.ne ha]
  simp only [Lev.wd, Lev.pol, Lev.idx, if_true, if_false, Bool.false_eq_true]
  rw [hsym (a' * K' + b) (a * K' + b')]
  generalize (!c.testBit (((a * K' + a') * K' + b) * K' + b')) = P
  generalize w (a * K' + b) (a' * K' + b') = w1
  generalize w (a * K' + b') (a' * K' + b) = w2
  have h1 := oddMin_le_left w1 w2
  have h2 := oddMin_le_right w1 w2
  have hf := sq_two_widths w1 w2 _ (dLen_cheap_le w1 w2)
  have hs1 : w1 - oddMin w1 w2 + dLen true (oddMin w1 w2) + (w2 - oddMin w1 w2) =
      w1 + w2 - 2 * oddMin w1 w2 + dLen true (oddMin w1 w2) := by omega
  have hs2 : w1 - oddMin w1 w2 + dLen false (oddMin w1 w2) + (w2 - oddMin w1 w2) = w1 + w2 := by
    simp only [dLen, Bool.false_eq_true, if_false]
    omega
  cases P
  · have e1 : (false == true) = false := rfl
    have e2 : (false == false) = true := rfl
    rw [e1, e2, hs1, hs2]
    exact hf
  · have e1 : (true == true) = true := rfl
    have e2 : (true == false) = false := rfl
    rw [e1, e2, hs1, hs2, add_comm ((w1 + w2 - _ + _) ^ 2)]
    exact hf

/-- Two words in one column: `a < a'` and `b = b'`. Only the direction of rows has wires here. -/
theorem quad_col {a a' : ℕ} (ha : a < a') (b : ℕ) : QuadIneq K' w c scale a a' b b := by
  unfold QuadIneq
  have hr : GG ⟨K', w, c, true, scale⟩ a a' b b = 2 * w (a * K' + b) (a' * K' + b) := by
    simp [GG, ha.ne, min_eq_left ha.le, max_eq_right ha.le, gg, seg_same, Lev.wd, two_mul]
  have hc : GG ⟨K', w, c, false, scale⟩ b b a a' = 0 := by simp [GG]
  rw [hr, hc]
  nlinarith [sq_nonneg (w (a * K' + b) (a' * K' + b))]

/-- Two words in one row: `a = a'` and `b < b'`. Only the direction of columns has wires here. -/
theorem quad_row (hsym : ∀ x y, w x y = w y x) (a : ℕ) {b b' : ℕ} (hb : b < b') :
    QuadIneq K' w c scale a a b b' := by
  unfold QuadIneq
  have hc : GG ⟨K', w, c, false, scale⟩ b b' a a = 2 * w (a * K' + b) (a * K' + b') := by
    simp [GG, hb.ne, min_eq_left hb.le, max_eq_right hb.le, gg, seg_same, Lev.wd, two_mul]
  have hr : GG ⟨K', w, c, true, scale⟩ a a b b' = 0 := by simp [GG]
  rw [hr, hc, hsym (a * K' + b') (a * K' + b)]
  nlinarith [sq_nonneg (w (a * K' + b) (a * K' + b'))]

/-- **One quadruple.** The inequality holds for all coordinates, in any order. -/
theorem quad_all (hsym : ∀ x y, w x y = w y x) (a a' b b' : ℕ) : QuadIneq K' w c scale a a' b b' := by
  have hb_case : ∀ {a a' : ℕ}, a < a' → ∀ b b', QuadIneq K' w c scale a a' b b' := by
    intro a a' ha b b'
    rcases lt_trichotomy b b' with hb | rfl | hb
    · exact quad_rect hsym ha hb
    · exact quad_col ha b
    · exact QuadIneq.swap_b (quad_rect hsym ha hb)
  rcases lt_trichotomy a a' with ha | rfl | ha
  · exact hb_case ha b b'
  · rcases lt_trichotomy b b' with hb | rfl | hb
    · exact quad_row hsym a hb
    · simp [QuadIneq, GG]
    · exact QuadIneq.swap_b (quad_row hsym a hb)
  · exact QuadIneq.swap_a hsym (hb_case ha b b')

end Two

/-- The two segments have at most as many new wires as the two diagonals have wires. -/
theorem gg_le (l : Lev) {u u' : ℕ} (hu : u ≠ u') (v v' : ℕ) :
    gg l u u' v v' ≤ l.w (l.wd u v) (l.wd u' v') + l.w (l.wd u v') (l.wd u' v) := by
  have hlt : ∀ {v v' : ℕ}, v < v' →
      gg l u u' v v' ≤ l.w (l.wd u v) (l.wd u' v') + l.w (l.wd u v') (l.wd u' v) := by
    intro v v' hv
    rw [gg_of_lt l hu hv]
    have h1 := oddMin_le_left (l.w (l.wd u v) (l.wd u' v')) (l.w (l.wd u v') (l.wd u' v))
    have h2 := oddMin_le_right (l.w (l.wd u v) (l.wd u' v')) (l.w (l.wd u v') (l.wd u' v))
    have h3 := dLen_le (l.pol u u' v v' == l.dir) (l.w (l.wd u v) (l.wd u' v')) (l.w (l.wd u v') (l.wd u' v))
    omega
  rcases lt_trichotomy v v' with hv | rfl | hv
  · exact hlt hv
  · simp [gg, seg_same]
  · have := hlt hv
    rw [gg, add_comm, ← gg, add_comm (l.w (l.wd u v) _)]
    exact this

/-- The new weight of a pair is at most the number of wires between its two rows. -/
theorem newW_le (l : Lev) (hsym : ∀ x y, l.w x y = l.w y x) (u u' : ℕ) :
    l.newW u u' ≤ ∑ v ∈ range l.K', ∑ v' ∈ range l.K', l.w (l.wd u v) (l.wd u' v') := by
  by_cases h : u = u'
  · subst h
    simp [Lev.newW]
  have h2 := two_newW l h
  have hA : min u u' ≠ max u u' := by
    rcases lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left h'.le, max_eq_right h'.le]
      exact h
    · rw [min_eq_right h'.le, max_eq_left h'.le]
      exact h'.ne
  have hle : ∑ v ∈ range l.K', ∑ v' ∈ range l.K', GG l u u' v v' ≤
      2 * ∑ v ∈ range l.K', ∑ v' ∈ range l.K', l.w (l.wd (min u u') v) (l.wd (max u u') v') := by
    rw [two_mul]
    nth_rw 2 [sum_comm]
    rw [← sum_add_distrib]
    refine sum_le_sum fun v _ => ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun v' _ => ?_
    simp only [GG, if_neg h]
    exact (gg_le l hA v v').trans_eq (add_comm _ _)
  have hmm : ∑ v ∈ range l.K', ∑ v' ∈ range l.K', l.w (l.wd (min u u') v) (l.wd (max u u') v') =
      ∑ v ∈ range l.K', ∑ v' ∈ range l.K', l.w (l.wd u v) (l.wd u' v') := by
    rcases lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left h'.le, max_eq_right h'.le]
    · rw [min_eq_right h'.le, max_eq_left h'.le, sum_comm]
      exact sum_congr rfl fun v _ => sum_congr rfl fun v' _ => hsym _ _
  rw [hmm] at hle
  omega

end Pot

/-! ### The theorems -/

/-- The sum over the two directions. -/
theorem potential_two (K' : ℕ) (w : ℕ → ℕ → ℕ) (hsym : ∀ x y, w x y = w y x) (c scale : ℕ) :
    25 * (psi K' (rowW K' w c scale) + psi K' (colW K' w c scale)) ≤ 48 * K' ^ 2 * psi (K' * K') w := by
  have hr : 4 * psi K' (rowW K' w c scale) ≤ K' ^ 2 * ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
      Pot.GG ⟨K', w, c, true, scale⟩ a a' b b' ^ 2 := Pot.four_psi_le ⟨K', w, c, true, scale⟩
  have hc : 4 * psi K' (colW K' w c scale) ≤ K' ^ 2 * ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
      Pot.GG ⟨K', w, c, false, scale⟩ b b' a a' ^ 2 := by
    rw [Pot.sum4_swap (range K') (range K') (fun a a' b b' => Pot.GG ⟨K', w, c, false, scale⟩ b b' a a' ^ 2)]
    exact Pot.four_psi_le ⟨K', w, c, false, scale⟩
  have hq : 25 * (∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
        Pot.GG ⟨K', w, c, true, scale⟩ a a' b b' ^ 2 +
      ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
        Pot.GG ⟨K', w, c, false, scale⟩ b b' a a' ^ 2) ≤
      96 * (2 * psi (K' * K') w) := by
    have hswap : ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
        w (a * K' + b') (a' * K' + b) ^ 2 = psi (K' * K') w := by
      rw [Pot.psi_digits]
      exact sum_congr rfl fun a _ => sum_congr rfl fun a' _ => sum_comm
    rw [two_mul]
    nth_rw 1 [← hswap]
    rw [Pot.psi_digits, ← sum_add_distrib, ← sum_add_distrib, mul_sum, mul_sum]
    refine sum_le_sum fun a _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib, mul_sum, mul_sum]
    refine sum_le_sum fun a' _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib, mul_sum, mul_sum]
    refine sum_le_sum fun b _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib, mul_sum, mul_sum]
    refine sum_le_sum fun b' _ => ?_
    have := Pot.quad_all (K' := K') (w := w) (c := c) (scale := scale) hsym a a' b b'
    unfold Pot.QuadIneq at this
    rw [add_comm (w (a * K' + b') _ ^ 2)]
    exact this
  have hmul : 100 * (psi K' (rowW K' w c scale) + psi K' (colW K' w c scale)) ≤
      4 * (48 * K' ^ 2 * psi (K' * K') w) := by
    calc 100 * (psi K' (rowW K' w c scale) + psi K' (colW K' w c scale))
        = 25 * (4 * psi K' (rowW K' w c scale) + 4 * psi K' (colW K' w c scale)) := by ring
      _ ≤ 25 * (K' ^ 2 * ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
            Pot.GG ⟨K', w, c, true, scale⟩ a a' b b' ^ 2 +
          K' ^ 2 * ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
            Pot.GG ⟨K', w, c, false, scale⟩ b b' a a' ^ 2) := by omega
      _ = K' ^ 2 * (25 * (∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
            Pot.GG ⟨K', w, c, true, scale⟩ a a' b b' ^ 2 +
          ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K',
            Pot.GG ⟨K', w, c, false, scale⟩ b b' a a' ^ 2)) := by ring
      _ ≤ K' ^ 2 * (96 * (2 * psi (K' * K') w)) := Nat.mul_le_mul_left _ hq
      _ = 4 * (48 * K' ^ 2 * psi (K' * K') w) := by ring
  omega

/-- **The smaller direction.** -/
theorem potential_min (K' : ℕ) (w : ℕ → ℕ → ℕ) (hsym : ∀ x y, w x y = w y x) (c scale : ℕ) :
    25 * psi K' (Lev.newW ⟨K', w, c, dirOf K' w scale c, scale⟩) ≤ 24 * K' ^ 2 * psi (K' * K') w := by
  have h := potential_two K' w hsym c scale
  have h48 : 48 * K' ^ 2 * psi (K' * K') w = 2 * (24 * K' ^ 2 * psi (K' * K') w) := by ring
  rw [h48] at h
  unfold dirOf
  by_cases hd : psi K' (rowW K' w c scale) ≤ psi K' (colW K' w c scale)
  · rw [decide_eq_true hd]
    change 25 * psi K' (rowW K' w c scale) ≤ _
    omega
  · rw [decide_eq_false hd]
    change 25 * psi K' (colW K' w c scale) ≤ _
    omega

set_option linter.unusedVariables false in
/-- The new weights are symmetric. -/
theorem newW_symm (l : Lev) (hsym : ∀ x y, l.w x y = l.w y x) (u u' : ℕ) : l.newW u u' = l.newW u' u := by
  simp only [Lev.newW, min_comm u u', max_comm u u', eq_comm]

/-- The new weights vanish on the diagonal. -/
theorem newW_self (l : Lev) (u : ℕ) : l.newW u u = 0 := by
  simp [Lev.newW]

set_option linter.unusedVariables false in
/-- The number of wires does not grow. -/
theorem newW_total_le (l : Lev) (hK : 0 < l.K') (hsym : ∀ x y, l.w x y = l.w y x) :
    ∑ u ∈ range l.K', ∑ u' ∈ range l.K', l.newW u u' ≤
      ∑ x ∈ range (l.K' * l.K'), ∑ y ∈ range (l.K' * l.K'), l.w x y := by
  calc ∑ u ∈ range l.K', ∑ u' ∈ range l.K', l.newW u u'
      ≤ ∑ u ∈ range l.K', ∑ u' ∈ range l.K', ∑ v ∈ range l.K', ∑ v' ∈ range l.K',
          l.w (l.wd u v) (l.wd u' v') :=
        sum_le_sum fun u _ => sum_le_sum fun u' _ => Pot.newW_le l hsym u u'
    _ = ∑ u ∈ range l.K', ∑ v ∈ range l.K', ∑ u' ∈ range l.K', ∑ v' ∈ range l.K',
          l.w (l.wd u v) (l.wd u' v') :=
        sum_congr rfl fun u _ => sum_comm
    _ = ∑ u ∈ range l.K', ∑ v ∈ range l.K', ∑ y ∈ range (l.K' * l.K'), l.w (l.wd u v) y :=
        sum_congr rfl fun u _ => sum_congr rfl fun v _ => Pot.sum_wd l _
    _ = _ := Pot.sum_wd l (fun x => ∑ y ∈ range (l.K' * l.K'), l.w x y)

/-- A weight is at most the total. -/
theorem le_total {K : ℕ} {w : ℕ → ℕ → ℕ} {x y : ℕ} (hx : x < K) (hy : y < K) :
    w x y ≤ ∑ x ∈ range K, ∑ y ∈ range K, w x y := by
  calc w x y ≤ ∑ y ∈ range K, w x y :=
        single_le_sum (f := fun y => w x y) (fun _ _ => Nat.zero_le _) (mem_range.mpr hy)
    _ ≤ _ := single_le_sum (f := fun x => ∑ y ∈ range K, w x y) (fun _ _ => Nat.zero_le _) (mem_range.mpr hx)

/-- The number of ends on the words of one `u`, by Cauchy. -/
theorem ends_row_sq_le (l : Lev) {u : ℕ} (hu : u < l.K') :
    (∑ v ∈ range l.K', ∑ y ∈ range (l.K' * l.K'), l.w (l.wd u v) y) ^ 2 ≤
      l.K' ^ 3 * psi (l.K' * l.K') l.w := by
  have h := Pot.sq_sum_sum_le (range l.K') (range (l.K' * l.K')) (fun v y => l.w (l.wd u v) y)
  simp only [card_range] at h
  have hsub : ∑ v ∈ range l.K', ∑ y ∈ range (l.K' * l.K'), l.w (l.wd u v) y ^ 2 ≤ psi (l.K' * l.K') l.w := by
    unfold psi
    rw [← Pot.sum_wd l (fun x => ∑ y ∈ range (l.K' * l.K'), l.w x y ^ 2)]
    exact single_le_sum (f := fun u => ∑ v ∈ range l.K', ∑ y ∈ range (l.K' * l.K'), l.w (l.wd u v) y ^ 2)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr hu)
  calc _ ≤ _ := h
    _ ≤ l.K' * (l.K' * l.K') * psi (l.K' * l.K') l.w := Nat.mul_le_mul_left _ hsub
    _ = _ := by ring

/-- The number of ends of a level, by Cauchy. -/
theorem ends_all_sq_le (K : ℕ) (w : ℕ → ℕ → ℕ) :
    (∑ x ∈ range K, ∑ y ∈ range K, w x y) ^ 2 ≤ K ^ 2 * psi K w := by
  have h := Pot.sq_sum_sum_le (range K) (range K) w
  simp only [card_range] at h
  calc _ ≤ _ := h
    _ = _ := by rw [psi]; ring

end UncrossingWires
