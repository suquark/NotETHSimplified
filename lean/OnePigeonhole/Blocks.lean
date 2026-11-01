import OnePigeonhole.Cube

/-!
# The matrix `H_{T,t,S}` on the cubes

Section 4 of `papers/one-pigeonhole/proof.tex`, on the wires, with the blocks that `Cube.lean` describes.

* `Wires.cornersOf`, `Wires.used`, `Wires.atCorner`: sets of wires and functions on wires, read on the corners of one cube.
* `Wires.cubeEquiv`: the wires of a cube are its corners in use.
* `letter_of_coefH_ne_zero`: equation (4). `letter_rowSide`, `letter_colSide`: the sides of `Cube.lean` stand for the letters of the text.
* `coefH_eq_cubeCoef`: the coefficient of an entry of `H_{T,t,S}` on the wires of a cube is the coefficient on their corners.
* `det_Hz_eq_prod`: `det H_{T,t,S}` is the product of the determinants of the cubes. Rows and columns of a cube are indexed by the
  same wires, so one simultaneous permutation of rows and columns makes the matrix block diagonal, and no sign appears.
* `xiOf`, `xTilde`, `det_Hz_eq_sum_U`: `det H = ∑_ξ det H^ξ ∏_{i ∈ S} [x_i = ξ_i]`, where `ξ` is given by the set `U` of the
  rows `i ∈ S` with `ξ_i = 1`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset TransposeBase MvPolynomial

variable {Q L h M : ℕ}

namespace Wires

variable (W : Wires Q L h M)

/-- The corners of the wires of `Z` in the cube of `k`. -/
def cornersOf (k : Key Q L h) (Z : Finset (Fin M)) : Finset (Corner Q) :=
  (Z.filter fun i => W.key i = k).image W.F

/-- The corners of the cube of `k` that hold a wire. -/
def used (k : Key Q L h) : Finset (Corner Q) := W.cornersOf k univ

theorem F_mem_cornersOf_iff {k : Key Q L h} {i : Fin M} (hi : W.key i = k) (Z : Finset (Fin M)) :
    W.F i ∈ W.cornersOf k Z ↔ i ∈ Z := by
  simp only [cornersOf, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨i', ⟨hZ, hk⟩, hF⟩
    rwa [← W.F_inj (hk.trans hi.symm) hF]
  · intro hZ
    exact ⟨i, ⟨hZ, hi⟩, rfl⟩

theorem F_mem_used {k : Key Q L h} {i : Fin M} (hi : W.key i = k) : W.F i ∈ W.used k :=
  (W.F_mem_cornersOf_iff hi univ).mpr (Finset.mem_univ i)

theorem exists_of_mem_used {k : Key Q L h} {a : Corner Q} (ha : a ∈ W.used k) :
    ∃ i, W.key i = k ∧ W.F i = a := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨i, (Finset.mem_filter.mp hi).2, rfl⟩

/-- The value at a corner of a function on the wires, and `0` at a corner without a wire. -/
def atCorner (k : Key Q L h) (f : Fin M → ℚ) (a : Corner Q) : ℚ :=
  ∑ i, if W.key i = k ∧ W.F i = a then f i else 0

/-- A wire is at the corner `a` of the cube of `k` exactly when its cell is the cell at this corner. -/
theorem key_F_iff_c_eq {k : Key Q L h} (hk : IsKey k) (i : Fin M) (a : Corner Q) :
    (W.key i = k ∧ W.F i = a) ↔ W.c i = corner k a := by
  rw [W.c_eq_corner i, corner_inj (W.isKey_key i) hk]

theorem atCorner_F {k : Key Q L h} {i : Fin M} (hi : W.key i = k) (f : Fin M → ℚ) :
    W.atCorner k f (W.F i) = f i := by
  unfold atCorner
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro i' _ hne
    rw [if_neg]
    rintro ⟨hk, hF⟩
    exact hne (W.F_inj (hk.trans hi.symm) hF)
  · simp

/-- The wires of a cube are its corners in use. -/
noncomputable def cubeEquiv (k : Key Q L h) : {i // W.key i = k} ≃ {a // a ∈ W.used k} :=
  Equiv.ofBijective (fun i => ⟨W.F i.1, W.F_mem_used i.2⟩) (by
    constructor
    · intro i j he
      have hF : W.F i.1 = W.F j.1 := congrArg Subtype.val he
      exact Subtype.ext (W.F_inj (i.2.trans j.2.symm) hF)
    · rintro ⟨a, ha⟩
      obtain ⟨i, hi, hF⟩ := W.exists_of_mem_used ha
      exact ⟨⟨i, hi⟩, Subtype.ext hF⟩)

@[simp] theorem cubeEquiv_apply (k : Key Q L h) (i : {i // W.key i = k}) :
    (W.cubeEquiv k i : Corner Q) = W.F i.1 := rfl

end Wires

/-! ### The letters -/

/-- **Equation (4).** A nonzero coefficient `γ_ij` has `c_i` and `d_j` in one cube. Then `τ_{E_ij} c_i = d_j`, and the first words at the
digit `t` give that the first-word letter of `d_j` is `g_i`: the letter `W.tw i t` if `i ∉ S`, and the letter `W.hw i t` if `i ∈ S`. -/
theorem letter_of_coefH_ne_zero (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) {i j : Fin M} (hne : coefH W κ R T t S i j ≠ 0) :
    W.key i = W.key j ∧ W.hw j t = if i ∈ S then W.hw i t else W.tw i t := by
  unfold coefH at hne
  split_ifs at hne with hE
  · have hk : W.key i = W.key j := by
      by_contra hk
      exact hne (by simp [coefT, hk])
    refine ⟨hk, ?_⟩
    have hτ := (W.tau_c_eq_d_iff_Eij (W.Eij i j) i j).mpr ⟨hk, rfl⟩
    have h1 := congrArg (fun c : LCell Q L h => c.1.1 t) hτ
    simp only [tau_fst_fst] at h1
    by_cases hS : i ∈ S
    · rw [if_pos hS]
      rw [if_pos (hE.mpr hS)] at h1
      exact h1.symm
    · rw [if_neg hS]
      rw [if_neg (fun h2 => hS (hE.mp h2))] at h1
      exact h1.symm
  · exact absurd rfl hne

/-- The side of a row stands for the letter `g_i` of the text. -/
theorem letter_rowSide (W : Wires Q L h M) (t : Fin Q) (S : Finset (Fin M)) {k : Key Q L h} {i : Fin M}
    (hi : W.key i = k) :
    letter k t (rowSide t (W.cornersOf k S) (W.F i)) = if i ∈ S then W.hw i t else W.tw i t := by
  by_cases hS : i ∈ S
  · have hF : W.F i ∈ W.cornersOf k S := (W.F_mem_cornersOf_iff hi S).mpr hS
    rw [if_pos hS, W.hw_eq_letter, hi]
    simp [rowSide, hF]
  · have hF : W.F i ∉ W.cornersOf k S := (W.F_mem_cornersOf_iff hi S).not.mpr hS
    rw [if_neg hS, W.tw_eq_letter, hi]
    simp [rowSide, hF]

/-- The side of a column stands for the first-word letter `o_j` of `d_j`. -/
theorem letter_colSide (W : Wires Q L h M) (t : Fin Q) {k : Key Q L h} {j : Fin M} (hj : W.key j = k) :
    letter k t (colSide t (W.F j)) = W.hw j t := by
  rw [W.hw_eq_letter, hj]
  rfl

/-! ### From the wires to the corners -/

/-- On the wires of one cube, the coefficient of `H_{T,t,S}` is the coefficient on their corners. -/
theorem coefH_eq_cubeCoef (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) {k : Key Q L h} {i j : Fin M} (hi : W.key i = k) (hj : W.key j = k) :
    coefH W κ R T t S i j =
      cubeCoef κ R t (W.cornersOf k T) (W.cornersOf k S) (W.F i) (W.F j) := by
  have hS := W.F_mem_cornersOf_iff hi S
  have hT := W.F_mem_cornersOf_iff hi T
  have hE : exch (W.F i) (W.F j) = W.Eij i j := rfl
  have hg : gamE κ R (W.cornersOf k T) (W.F i) (W.Eij i j) = gamE κ R T i (W.Eij i j) := by
    simp only [gamE, hT]
  simp only [coefH, coefT, cubeCoef, hE, hS, hg, if_pos (hi.trans hj.symm)]

/-- An entry of `H_{T,t,S}` between two cubes is `0`, since `E_ij` is only used within a cube. -/
theorem Hz_eq_zero_of_key (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (x y : Fin M → ℚ) {i j : Fin M} (hk : W.key i ≠ W.key j) :
    Hz W κ R T t S x y i j = 0 := by
  simp [Hz, coefH, coefT, hk]

/-- **The product over the cubes.** Rows and columns of a cube are indexed by the same wires, so there is no sign. -/
theorem det_Hz_eq_prod (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (x y : Fin M → ℚ) :
    (Hz W κ R T t S x y).det =
      ∏ k ∈ keys Q L h, (cubeMat κ R t (W.used k) (W.cornersOf k T) (W.cornersOf k S)
        (W.atCorner k x) (W.atCorner k y)).det := by
  classical
  rw [det_block_by _ W.key (fun i j hk => Hz_eq_zero_of_key W κ R T t S x y hk)]
  rw [← Finset.prod_subset (Finset.subset_univ (keys Q L h))]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Matrix.det_submatrix_equiv_self (W.cubeEquiv k)]
    congr 1
    ext1 i j
    show coefH W κ R T t S i.1 j.1 * C (eqv (x i.1) (y j.1)) =
      cubeCoef κ R t (W.cornersOf k T) (W.cornersOf k S) (W.F i.1) (W.F j.1) *
        C (eqv (W.atCorner k x (W.F i.1)) (W.atCorner k y (W.F j.1)))
    rw [coefH_eq_cubeCoef W κ R T t S i.2 j.2, W.atCorner_F i.2, W.atCorner_F j.2]
  · intro k _ hk
    have hemp : IsEmpty {i // W.key i = k} :=
      ⟨fun i => hk (i.2 ▸ W.key_mem_keys i.1)⟩
    exact Matrix.det_isEmpty

/-! ### The rows of `S` -/

/-- The number `ξ_i` of the set `U`: `1` if `i ∈ U`, and `0` if not. -/
def xiOf (U : Finset (Fin M)) (i : Fin M) : ℚ := if i ∈ U then 1 else 0

/-- `x̃`: the number `ξ_i` on the rows `i ∈ S`, and `x_i` on the other rows. So `H^ξ` is `H_{T,t,S}` with `x̃` for `x`. -/
def xTilde (S U : Finset (Fin M)) (x : Fin M → ℚ) (i : Fin M) : ℚ := if i ∈ S then xiOf U i else x i

/-- **The numbers `ξ`.** `det H = ∑_ξ det H^ξ ∏_{i ∈ S} [x_i = ξ_i]`. It holds for all rationals `x`, `y`. -/
theorem det_Hz_eq_sum_U (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (x y : Fin M → ℚ) :
    (Hz W κ R T t S x y).det =
      ∑ U ∈ S.powerset, C (∏ i ∈ S, eqv (x i) (xiOf U i)) * (Hz W κ R T t S (xTilde S U x) y).det := by
  classical
  let γ := coefH W κ R T t S
  let A : Matrix (Fin M) (Fin M) (Pz Q) :=
    Matrix.of fun i j => if i ∈ S then C (eqv (x i) 1) * (γ i j * C (eqv 1 (y j))) else 0
  let B : Matrix (Fin M) (Fin M) (Pz Q) :=
    Matrix.of fun i j => if i ∈ S then C (eqv (x i) 0) * (γ i j * C (eqv 0 (y j)))
      else γ i j * C (eqv (x i) (y j))
  have hAB : Hz W κ R T t S x y = A + B := by
    ext1 i j
    by_cases hi : i ∈ S
    · simp only [Hz, A, B, γ, Matrix.add_apply, Matrix.of_apply, if_pos hi]
      rw [eqv_split (x i) (y j), map_add, map_mul, map_mul]
      ring
    · simp [Hz, A, B, γ, hi]
  rw [hAB, det_add_eq_sum_rowMix, ← Finset.sum_subset (Finset.subset_univ S.powerset)]
  · refine Finset.sum_congr rfl fun U hU => ?_
    have hU' := Finset.mem_powerset.mp hU
    have hmat : rowMix U A B = Matrix.of fun i j =>
        (if i ∈ S then C (eqv (x i) (xiOf U i)) else 1) * Hz W κ R T t S (xTilde S U x) y i j := by
      ext1 i j
      by_cases hiU : i ∈ U
      · have hiS := hU' hiU
        simp [A, γ, Hz, xTilde, xiOf, hiU, hiS]
      · by_cases hiS : i ∈ S
        · simp [B, γ, Hz, xTilde, xiOf, hiU, hiS]
        · simp [B, γ, Hz, xTilde, hiU, hiS]
    rw [hmat, Matrix.det_mul_column, Finset.prod_ite_mem, Finset.univ_inter, map_prod]
  · intro V _ hV
    obtain ⟨i, hi, hiS⟩ := Finset.not_subset.mp fun hsub => hV (Finset.mem_powerset.mpr hsub)
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    simp [A, hi, hiS]

end OnePigeonhole
