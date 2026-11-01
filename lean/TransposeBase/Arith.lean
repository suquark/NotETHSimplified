import TransposeBase.Short

/-!
# Counting and arithmetic -/

namespace TransposeBase
open scoped BigOperators
open Finset

variable {Q : ℕ} {A : Type*}

section Count

theorem card_small_le {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ} (hL : 1 < L) :
    ((((Finset.univ : Finset (Finset α)).filter
        (fun S => S.card < Fintype.card α / L + 1)).card : ℕ) : ℝ)
      ≤ Real.exp ((Real.log L + 1) * Fintype.card α / L) := by
  set N := Fintype.card α
  set j := N / L
  have hl : (1 : ℝ) < L := by exact_mod_cast hL
  have hl0 : (0 : ℝ) < L := by linarith
  have h1 : ((((Finset.univ : Finset (Finset α)).filter
      (fun S => S.card < j + 1)).card : ℕ) : ℝ)
        ≤ ∑ S : Finset α, (L : ℝ) ^ j * ((L : ℝ)⁻¹ ^ S.card * 1 ^ (N - S.card)) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine (Finset.sum_le_sum (g := fun S : Finset α =>
      (L : ℝ) ^ j * ((L : ℝ)⁻¹ ^ S.card * 1 ^ (N - S.card))) fun S hS => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => by positivity)
    have hS' : S.card ≤ j := Nat.lt_succ_iff.mp (Finset.mem_filter.mp hS).2
    have hpow : (L : ℝ) ^ j = (L : ℝ) ^ (j - S.card) * (L : ℝ) ^ S.card := by
      rw [← pow_add, Nat.sub_add_cancel hS']
    simp only [one_pow, mul_one, Nat.cast_one]
    rw [hpow, mul_assoc, ← mul_pow, mul_inv_cancel₀ hl0.ne', one_pow, mul_one]
    exact one_le_pow₀ hl.le
  have h2 : ∑ S : Finset α, (L : ℝ) ^ j * ((L : ℝ)⁻¹ ^ S.card * 1 ^ (N - S.card))
      = (L : ℝ) ^ j * ((L : ℝ)⁻¹ + 1) ^ N := by
    rw [← Finset.mul_sum, ← Finset.powerset_univ]
    congr 1
    exact Finset.sum_pow_mul_eq_add_pow _ _ _
  have h3 : ((L : ℝ)⁻¹ + 1) ^ N ≤ Real.exp ((N : ℝ) / L) := by
    have h : (L : ℝ)⁻¹ + 1 ≤ Real.exp (L : ℝ)⁻¹ := Real.add_one_le_exp _
    calc ((L : ℝ)⁻¹ + 1) ^ N ≤ Real.exp (L : ℝ)⁻¹ ^ N := pow_le_pow_left₀ (by positivity) h N
      _ = Real.exp ((N : ℝ) / L) := by
        rw [← Real.exp_nat_mul, div_eq_mul_inv]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hl.le
  have h4 : (L : ℝ) ^ j ≤ Real.exp (Real.log L * ((N : ℝ) / L)) := by
    have hj : (j : ℝ) ≤ (N : ℝ) / L := Nat.cast_div_le
    calc (L : ℝ) ^ j = Real.exp (j * Real.log L) := by
          rw [Real.exp_nat_mul, Real.exp_log hl0]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  rw [h2] at h1
  refine h1.trans ((mul_le_mul h4 h3 (by positivity) (Real.exp_pos _).le).trans (le_of_eq ?_))
  rw [← Real.exp_add]
  congr 1
  ring

end Count

/-! ### The choice of the parameters -/

/-- The choice of `L`. It uses `(log L + 2) / L → 0`. -/
theorem exists_good_L {D : ℕ} (hD : 1 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, 80 ≤ L ∧ 10 * (D : ℝ) ^ 2 * ((Real.log L + 2) / L) ≤ ε / 2 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  set δ : ℝ := ε / (20 * (D : ℝ) ^ 2) with hδ
  have hδ0 : 0 < δ := by positivity
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ δ / 2 * x := by
    filter_upwards [Real.isLittleO_log_id_atTop.bound (half_pos hδ0),
      Filter.eventually_ge_atTop 1] with x hx hx1
    have hx0 : (0 : ℝ) ≤ x := by linarith
    rw [Real.norm_eq_abs, id, Real.norm_eq_abs, abs_of_nonneg hx0] at hx
    exact (le_abs_self _).trans hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ δ / 2 * x := by
    filter_upwards [Filter.eventually_ge_atTop (4 / δ)] with x hx
    rw [div_le_iff₀ hδ0] at hx
    linarith
  have h3 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (h1.and h2)
  obtain ⟨L, hL80, hl1, hl2⟩ := ((Filter.eventually_ge_atTop 80).and h3).exists
  refine ⟨L, hL80, ?_⟩
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hle : (Real.log L + 2) / L ≤ δ := by
    rw [div_le_iff₀ hL0]
    linarith
  calc 10 * (D : ℝ) ^ 2 * ((Real.log L + 2) / L) ≤ 10 * (D : ℝ) ^ 2 * δ := by gcongr
    _ = ε / 2 := by
      rw [hδ]
      field_simp
      ring

section Words

variable [Fintype A] [DecidableEq A] {k : Type*} [CommRing k]

/-- The words with a prescribed digit. -/
theorem card_words_digit (t : Fin Q) (g : A) :
    (univ.filter fun w : Word Q A => w t = g).card * Fintype.card A = Fintype.card A ^ Q := by
  have h : ∀ b : A, (univ.filter fun w : Word Q A => w t = b).card =
      (univ.filter fun w : Word Q A => w t = g).card := by
    intro b
    refine card_bij' (fun w _ => Function.update w t g) (fun w _ => Function.update w t b)
      (by intro w _; simp) (by intro w _; simp) ?_ ?_
    · intro w hw
      have hb : w t = b := (mem_filter.mp hw).2
      funext i
      by_cases hi : i = t
      · subst hi
        simp [hb]
      · simp [Function.update_of_ne hi]
    · intro w hw
      have hb : w t = g := (mem_filter.mp hw).2
      funext i
      by_cases hi : i = t
      · subst hi
        simp [hb]
      · simp [Function.update_of_ne hi]
  have hsum : ∑ b : A, (univ.filter fun w : Word Q A => w t = b).card =
      (univ : Finset (Word Q A)).card :=
    (card_eq_sum_card_fiberwise fun w _ => mem_univ (w t)).symm
  simp only [h, sum_const, card_univ, smul_eq_mul, Fintype.card_pi, prod_const,
    Fintype.card_fin] at hsum
  rw [mul_comm]
  simpa using hsum

/-- A sum over all bits of a product over the fibres of `b` of functions of one fibre is the
product of the fibre sums. -/
theorem sum_prod_fibers {I κ : Type*} [Fintype I] [DecidableEq I] [Fintype κ] [DecidableEq κ]
    (b : I → κ) (F : (g : κ) → ({i // b i = g} → Bool) → k) :
    ∑ u : I → Bool, ∏ g, F g (fun i => u i.1) = ∏ g, ∑ v : {i // b i = g} → Bool, F g v := by
  rw [Fintype.prod_sum]
  let e : (I → Bool) ≃ ((g : κ) → {i // b i = g} → Bool) :=
    { toFun := fun u g i => u i.1
      invFun := fun v i => v (b i) ⟨i, rfl⟩
      left_inv := fun _ => rfl
      right_inv := by
        intro v
        funext g i
        obtain ⟨i, rfl⟩ := i
        rfl }
  exact e.sum_comp (fun v => ∏ g, F g (v g))

/-- A sum over two bit assignments is a sum over one assignment of the disjoint union. -/
theorem sum_bool_pair {E : Type*} [Fintype E] [DecidableEq E] (F : (E → Bool) → (E → Bool) → k) :
    ∑ x, ∑ y, F x y = ∑ u : E ⊕ E → Bool, F (u ∘ Sum.inl) (u ∘ Sum.inr) := by
  rw [← Fintype.sum_prod_type']
  exact ((Equiv.sumArrowEquivProdArrow E E Bool).sum_comp (fun p => F p.1 p.2)).symm

end Words

end TransposeBase
