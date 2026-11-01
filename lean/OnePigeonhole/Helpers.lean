import TransposeBase.Defs
import TransposeBase.Arith
import Mathlib

/-! Facts on determinants, degrees and small counts used by the proof of this library. -/

section

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset

section Mix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The rows in `S` come from `A`, the other rows from `B`. -/
def rowMix (S : Finset n) (A B : Matrix n n R) : Matrix n n R :=
  Matrix.of fun i j => if i ∈ S then A i j else B i j

@[simp] theorem rowMix_apply (S : Finset n) (A B : Matrix n n R) (i j : n) :
    rowMix S A B i j = if i ∈ S then A i j else B i j := rfl

theorem rowMix_eq_piecewise (S : Finset n) (A B : Matrix n n R) :
    rowMix S A B = S.piecewise (fun i => A i) (fun i => B i) := by
  ext i j
  by_cases h : i ∈ S <;> simp [rowMix, Finset.piecewise, h]

theorem det_add_eq_sum_rowMix (A B : Matrix n n R) :
    (A + B).det = ∑ S : Finset n, (rowMix S A B).det := by
  have h := (Matrix.detRowAlternating (n := n) (R := R)).toMultilinearMap.map_add_univ
    (fun i => A i) (fun i => B i)
  have e : ((fun i => A i) + (fun i => B i) : n → n → R) = (A + B : Matrix n n R) := by
    ext i j
    simp
  rw [e] at h
  refine h.trans (Finset.sum_congr rfl fun S _ => ?_)
  rw [rowMix_eq_piecewise]
  rfl

end Mix

section Field

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

theorem det_rowMix_eq_zero (S : Finset n) (A B : Matrix n n K) (V : Submodule K (n → K))
    (hV : ∀ i ∈ S, A i ∈ V) (hcard : Module.finrank K V < S.card) :
    (rowMix S A B).det = 0 := by
  by_contra hne
  have hli : LinearIndependent K (fun i => rowMix S A B i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hne
  let f : S → V := fun i => ⟨A i.1, hV i.1 i.2⟩
  have hf : LinearIndependent K f := by
    refine LinearIndependent.of_comp V.subtype ?_
    have e : (⇑V.subtype ∘ f) = (fun i => rowMix S A B i) ∘ (fun i : S => i.1) := by
      funext i
      funext j
      simp [f, rowMix, i.2]
    rw [e]
    exact hli.comp _ Subtype.val_injective
  have := hf.fintype_card_le_finrank
  simp only [Fintype.card_coe] at this
  omega

end Field

end OnePigeonhole

end

section

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset TransposeBase MvPolynomial

section DetPoly

variable {n σ : Type*} [Fintype n] [DecidableEq n] [Fintype σ] [DecidableEq σ]

abbrev P (σ : Type*) := MvPolynomial σ ℚ

theorem det_expand (M : Matrix n n (P σ)) :
    M.det = ∑ s : Equiv.Perm n, ((Equiv.Perm.sign s : ℤ) : P σ) * ∏ i, M (s i) i :=
  Matrix.det_apply' M

theorem totalDegree_intCast_mul_le (z : ℤ) (p : P σ) :
    (((z : ℤ) : P σ) * p).totalDegree ≤ p.totalDegree := by
  refine (totalDegree_mul _ _).trans ?_
  have : ((z : ℤ) : P σ) = C ((z : ℤ) : ℚ) := by simp
  rw [this, totalDegree_C, zero_add]

theorem totalDegree_det_le (M : Matrix n n (P σ)) (b : n → ℕ)
    (h : ∀ i j, (M i j).totalDegree ≤ b i) : M.det.totalDegree ≤ ∑ i, b i := by
  rw [det_expand]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => ?_)
  refine (totalDegree_intCast_mul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (s i) i).totalDegree ≤ ∑ i, b (s i) := Finset.sum_le_sum fun i _ => h _ _
    _ = ∑ i, b i := Equiv.sum_comp s b

theorem degreeOf_intCast_mul_le (i : σ) (z : ℤ) (p : P σ) :
    degreeOf i (((z : ℤ) : P σ) * p) ≤ degreeOf i p := by
  refine (degreeOf_mul_le _ _ _).trans ?_
  have : ((z : ℤ) : P σ) = C ((z : ℤ) : ℚ) := by simp
  rw [this, degreeOf_C, zero_add]

theorem degreeOf_det_le (M : Matrix n n (P σ)) (v : σ)
    (h : ∀ i j, degreeOf v (M i j) ≤ 1) : degreeOf v M.det ≤ Fintype.card n := by
  rw [det_expand]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun s _ => ?_)
  refine (degreeOf_intCast_mul_le _ _ _).trans ?_
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ i, degreeOf v (M (s i) i) ≤ ∑ _i : n, 1 := Finset.sum_le_sum fun i _ => h _ _
    _ = Fintype.card n := by simp

/-- If the rows in `S` are divisible by `d`, then `d ^ |S|` divides the determinant. -/
theorem pow_card_dvd_det {R : Type*} [CommRing R] (M : Matrix n n R) (S : Finset n) (d : R)
    (h : ∀ i ∈ S, ∀ j, d ∣ M i j) : d ^ S.card ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  refine Finset.dvd_sum fun s _ => Dvd.dvd.mul_left ?_ _
  have hprod : ∏ i, M (s i) i = ∏ i, M i (s⁻¹ i) := by
    rw [← Equiv.prod_comp s (fun i => M i (s⁻¹ i))]
    simp
  rw [hprod, ← Finset.prod_filter_mul_prod_filter_not univ (fun i => i ∈ S)]
  refine Dvd.dvd.mul_right ?_ _
  have hS : univ.filter (fun i => i ∈ S) = S := by
    ext i
    simp
  rw [hS, ← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi => h i hi _

end DetPoly

variable {Q : ℕ} {A : Type*} [Fintype A] [LinearOrder A]

variable (κ : Finset (Fin Q) → ℚ) (R r : ℕ) (X Y : Cell Q A → ℚ)

theorem degreeOf_yMono_le' (i : Fin Q) (E : Finset (Fin Q)) :
    degreeOf i (yMono (k := ℚ) E : P (Fin Q)) ≤ 1 :=
  degreeOf_yMono_le (k := ℚ) i E

theorem degreeOf_C_mul_le' {p : P (Fin Q)} {d : ℕ} (i : Fin Q) (a : ℚ)
    (hp : degreeOf i p ≤ d) : degreeOf i (C a * p) ≤ d :=
  degreeOf_C_mul_le (k := ℚ) i a hp

theorem degreeOf_mul_C_le {p : P (Fin Q)} {d : ℕ} (i : Fin Q) (a : ℚ) (hp : degreeOf i p ≤ d) :
    degreeOf i (p * C a) ≤ d := by
  rw [mul_comm]
  exact degreeOf_C_mul_le' i a hp

variable {Q : ℕ}

abbrev Pos (Q : ℕ) := Finset (Fin Q)

/-- A determinant vanishes if more rows than columns live on one set of columns. -/
theorem det_eq_zero_of_rows {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] (M : Matrix n n R)
    (Rw Cl : Finset n) (h : ∀ i ∈ Rw, ∀ j ∉ Cl, M i j = 0) (hc : Cl.card < Rw.card) : M.det = 0 := by
  classical
  rw [Matrix.det_apply']
  refine Finset.sum_eq_zero fun s _ => ?_
  have hprod : ∏ i, M (s i) i = ∏ i, M i (s⁻¹ i) := by
    rw [← Equiv.prod_comp s (fun i => M i (s⁻¹ i))]
    simp
  rw [hprod]
  have himg : (Rw.image ⇑s⁻¹).card = Rw.card := Finset.card_image_of_injective _ (Equiv.injective _)
  obtain ⟨j, hj, hjC⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := Cl) (t := Rw.image ⇑s⁻¹) (by omega)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  have : ∏ i, M i (s⁻¹ i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h i hi _ hjC)
  rw [this, mul_zero]

variable {Q : ℕ} {A : Type*} [Fintype A] [LinearOrder A]

/-- A matrix without entries between different blocks is the product of its blocks. -/
theorem det_block_by {n β R : Type*} [Fintype n] [DecidableEq n] [Fintype β] [DecidableEq β] [CommRing R]
    (M : Matrix n n R) (b : n → β) (h : ∀ i j, b i ≠ b j → M i j = 0) :
    M.det = ∏ x, (M.toSquareBlock b x).det := by
  classical
  let _ : LinearOrder β := LinearOrder.lift' (Fintype.equivFin β) (Equiv.injective _)
  have hM : M.BlockTriangular b := fun i j hij => h i j (ne_of_gt hij)
  exact hM.det_fintype

variable (κ : Pos Q → ℚ) (R : ℕ) (t : Fin Q) (X Y : Cell Q A → ℚ) (L S U : Finset (Cell Q A))

variable {Q : ℕ} {A : Type*} [Fintype A] [LinearOrder A]

/-- The number of masks with fewer than `2 * (N / L) + 1` elements. -/
theorem card_few_le {α : Type*} [Fintype α] [DecidableEq α] {L : ℕ} (hL : 40 ≤ L) :
    (((univ : Finset (Finset α)).filter fun S => S.card < 2 * (Fintype.card α / L) + 1).card : ℝ) ≤
      Real.exp (3 * (Real.log L + 1) * Fintype.card α / L) := by
  set N := Fintype.card α with hN
  have hL2 : 1 < L / 2 := by omega
  have hsub : ((univ : Finset (Finset α)).filter fun S => S.card < 2 * (N / L) + 1) ⊆
      (univ : Finset (Finset α)).filter fun S => S.card < N / (L / 2) + 1 := by
    intro S hS
    have h1 : S.card < 2 * (N / L) + 1 := (Finset.mem_filter.mp hS).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h2 : 2 * (N / L) ≤ N / (L / 2) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc 2 * (N / L) * (L / 2) ≤ (N / L) * L := by
            have : 2 * (L / 2) ≤ L := Nat.mul_div_le L 2
            nlinarith [Nat.zero_le (N / L)]
        _ ≤ N := Nat.div_mul_le_self N L
    omega
  have hcard := Finset.card_le_card hsub
  have hsmall := card_small_le (α := α) hL2
  rw [← hN] at hsmall
  refine (Nat.cast_le.mpr hcard).trans (hsmall.trans (Real.exp_le_exp.mpr ?_))
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hL20 : (0 : ℝ) < ((L / 2 : ℕ) : ℝ) := by
    have : 0 < L / 2 := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hle : ((L / 2 : ℕ) : ℝ) ≤ L := by
    exact_mod_cast Nat.div_le_self L 2
  have hge : (L : ℝ) ≤ 3 * ((L / 2 : ℕ) : ℝ) := by
    have : L ≤ 3 * (L / 2) := by omega
    exact_mod_cast this
  have hlog : Real.log ((L / 2 : ℕ) : ℝ) ≤ Real.log L := Real.log_le_log hL20 hle
  have hlogL : 0 ≤ Real.log L + 1 := by
    have : 0 ≤ Real.log L := Real.log_nonneg (by
      have : 1 ≤ L := by omega
      exact_mod_cast this)
    linarith
  have h1 : (Real.log ((L / 2 : ℕ) : ℝ) + 1) * N ≤ (Real.log L + 1) * N :=
    mul_le_mul_of_nonneg_right (by linarith) hN0
  have h2 : (Real.log ((L / 2 : ℕ) : ℝ) + 1) * N / ((L / 2 : ℕ) : ℝ) ≤ (Real.log L + 1) * N / ((L / 2 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right h1 hL20.le
  refine h2.trans ?_
  rw [div_le_div_iff₀ hL20 hL0]
  have h3 : 0 ≤ (Real.log L + 1) * N := mul_nonneg hlogL hN0
  nlinarith

end OnePigeonhole

end
