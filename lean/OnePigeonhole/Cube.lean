import OnePigeonhole.Helpers
import OnePigeonhole.Pigeon

/-!
# One cube

The determinant across a digit `t`, on one cube. This refines Section 4 of `papers/one-pigeonhole/proof.tex`, where the blocks
are indexed by the letters: here a block is a cube and a side of the digit `t`, so its order is at most `2 ^ Q`.

The file has no wires. A row or a column is a corner `a`, a set of digits. In the sets of corners, `D` holds the corners in use,
`PT` the corners of the rows in `T`, and `PS` the corners of the rows in `S`. The functions `xv`, `yv` give the bits at the corners.
A row at the corner `ρ` is the cell `corner k ρ`, and a column at the corner `a` is the cell `corner k aᶜ`. So `exch ρ a = ρ ∆ aᶜ`
is the exchange from the row to the column.

A side is a value of `Bool`, and it stands for one of the two letters of the digit `t`. `rowSide t PS ρ` is the side of the letter
`g_i` of a row, and `colSide t a` is the side of the first-word letter of a column.

* `cubeCoef_eq_zero`: equation (4) on a cube: a nonzero coefficient has its row and its column on one side.
* `Balanced t D PS`: the two sides have as many rows as columns.
* `pairOf t D PS`: a permutation of the corners that moves to each column side the rows of that side.
* `cubeSign t D PS`: the sign of `pairOf`, and `0` if the cube is not balanced.
* `sideMat`, `sidePoly`: the matrix of one side, and its determinant, a polynomial in `z`.
* `det_cubeMat`: `det = cubeSign * side true * side false`.
* `sidePoly_congr`: the side `b` reads the bits only on the rows and the columns of the side `b`.
* `sidePoly_exp_le`: its exponents are at most `2 ^ Q`.
* `sideS`: the side with the sign of the cube on the side `false`, so that `prod_sideS`: the two sides with the sign are the determinant.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset TransposeBase MvPolynomial

variable {Q : ℕ}

/-! ### Rows and columns with two sides -/

section Split

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- If as many rows as columns have the side `true`, then a permutation moves to each column a row of the side of this
column. -/
theorem exists_perm_sides (rs cs : n → Bool)
    (hcard : (univ.filter fun a => rs a = true).card = (univ.filter fun a => cs a = true).card) :
    ∃ π : Equiv.Perm n, ∀ a, rs (π a) = cs a := by
  classical
  have hc : Fintype.card {a // cs a = true} = Fintype.card {a // rs a = true} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, hcard]
  let e : {a // cs a = true} ≃ {a // rs a = true} := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, fun a => ?_⟩
  by_cases ha : cs a = true
  · rw [ha]
    exact e.extendSubtype_mem a ha
  · have h1 := e.extendSubtype_not_mem a ha
    rw [Bool.not_eq_true] at ha h1
    rw [ha, h1]

/-- **The determinant with two sides.** If a nonzero entry has its row and its column on one side, and `π` moves to each
column a row of its side, then the determinant is the sign of `π` times the determinants of the two sides. -/
theorem det_eq_sign_mul_sides (N : Matrix n n R) (rs cs : n → Bool) (hN : ∀ i j, rs i ≠ cs j → N i j = 0)
    (π : Equiv.Perm n) (hπ : ∀ a, rs (π a) = cs a) :
    N.det = ((Equiv.Perm.sign π : ℤ) : R) * ∏ b : Bool, ((N.submatrix π id).toSquareBlock cs b).det := by
  classical
  have hblock : (N.submatrix π id).det = ∏ b : Bool, ((N.submatrix π id).toSquareBlock cs b).det :=
    det_block_by _ cs fun i j hij => by
      simp only [Matrix.submatrix_apply, id]
      exact hN _ _ (by rw [hπ]; exact hij)
  have hsign : ((Equiv.Perm.sign π : ℤ) : R) * ((Equiv.Perm.sign π : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1 <;> simp [h1]
  rw [← hblock, Matrix.det_permute, ← mul_assoc, hsign, one_mul]

/-- If the side `true` has different numbers of rows and columns, then some side has more rows than columns, and the
determinant is `0`. -/
theorem det_eq_zero_of_card_ne (N : Matrix n n R) (rs cs : n → Bool) (hN : ∀ i j, rs i ≠ cs j → N i j = 0)
    (hcard : (univ.filter fun a => rs a = true).card ≠ (univ.filter fun a => cs a = true).card) :
    N.det = 0 := by
  classical
  have hsum : ∀ f : n → Bool, (univ.filter fun a => f a = true).card + (univ.filter fun a => f a = false).card =
      Fintype.card n := by
    intro f
    rw [← Finset.card_union_of_disjoint, ← Finset.card_univ]
    · congr 1
      ext a
      cases f a <;> simp
    · rw [Finset.disjoint_left]
      intro a h1 h2
      have h3 := (Finset.mem_filter.mp h1).2
      have h4 := (Finset.mem_filter.mp h2).2
      rw [h3] at h4
      exact Bool.noConfusion h4
  have h1 := hsum rs
  have h2 := hsum cs
  rcases Nat.lt_or_gt_of_ne hcard with hlt | hgt
  · refine det_eq_zero_of_rows N (univ.filter fun a => rs a = false) (univ.filter fun a => cs a = false) ?_ (by omega)
    intro i hi j hj
    refine hN i j ?_
    have h3 := (Finset.mem_filter.mp hi).2
    have h4 : cs j = true := by simpa using hj
    rw [h3, h4]
    simp
  · refine det_eq_zero_of_rows N (univ.filter fun a => rs a = true) (univ.filter fun a => cs a = true) ?_ hgt
    intro i hi j hj
    refine hN i j ?_
    have h3 := (Finset.mem_filter.mp hi).2
    have h4 : cs j = false := by simpa using hj
    rw [h3, h4]
    simp

end Split

/-! ### The cube -/

/-- A corner of a cube: the digits exchanged from the base of the cube. -/
abbrev Corner (Q : ℕ) := Finset (Fin Q)

/-- The exchange from the cell at the corner `ρ` to the cell at the corner `aᶜ`. -/
def exch (ρ a : Corner Q) : Finset (Fin Q) := symmDiff ρ aᶜ

theorem mem_exch {t : Fin Q} {ρ a : Corner Q} : t ∈ exch ρ a ↔ (t ∈ ρ ↔ t ∈ a) := by
  simp only [exch, Finset.mem_symmDiff, Finset.mem_compl]
  tauto

/-- The side of a row. A row off `PS` has the side of the first-word letter of its cell, which is `true` when `t ∈ ρ`. A row in
`PS` has the side of the second-word letter. -/
def rowSide (t : Fin Q) (PS : Finset (Corner Q)) (ρ : Corner Q) : Bool :=
  xor (decide (t ∈ ρ)) (decide (ρ ∈ PS))

/-- The side of a column: the side of the first-word letter of the cell at `aᶜ`, which is `true` when `t ∉ a`. -/
def colSide (t : Fin Q) (a : Corner Q) : Bool := !decide (t ∈ a)

/-- The coefficient `γ` of an entry on a cube: the entries with `t ∈ exch ρ a` stay in the rows of `PS`, and the entries with
`t ∉ exch ρ a` stay in the other rows. -/
noncomputable def cubeCoef (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (PT PS : Finset (Corner Q)) (ρ a : Corner Q) : Pz Q :=
  if t ∈ exch ρ a ↔ ρ ∈ PS then C (gamE κ R PT ρ (exch ρ a)) * zMono (exch ρ a) else 0

/-- **Equation (4) on a cube.** A nonzero coefficient has its row and its column on one side. -/
theorem cubeCoef_eq_zero (κ : ℕ → ℚ) (R : ℕ) {t : Fin Q} (PT : Finset (Corner Q)) {PS : Finset (Corner Q)}
    {ρ a : Corner Q} (hne : rowSide t PS ρ ≠ colSide t a) : cubeCoef κ R t PT PS ρ a = 0 := by
  unfold cubeCoef
  rw [if_neg]
  intro hiff
  apply hne
  rw [mem_exch] at hiff
  by_cases h1 : t ∈ ρ <;> by_cases h2 : t ∈ a <;> by_cases h3 : ρ ∈ PS <;>
    simp_all [rowSide, colSide]

theorem degreeOf_cubeCoef_le (κ : ℕ → ℚ) (R : ℕ) (t v : Fin Q) (PT PS : Finset (Corner Q)) (ρ a : Corner Q) :
    degreeOf v (cubeCoef κ R t PT PS ρ a) ≤ 1 := by
  unfold cubeCoef
  split_ifs
  · exact degreeOf_C_mul_le' v _ (degreeOf_yMono_le' v _)
  · simp

/-- The matrix of a cube on its corners in use. -/
noncomputable def cubeMat (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) (xv yv : Corner Q → ℚ) :
    Matrix {a // a ∈ D} {a // a ∈ D} (Pz Q) :=
  Matrix.of fun ρ a => cubeCoef κ R t PT PS ρ.1 a.1 * C (eqv (xv ρ.1) (yv a.1))

/-- The side `true` has as many rows as columns. Then the side `false` also has, since `D` indexes both the rows and the
columns. -/
def Balanced (t : Fin Q) (D PS : Finset (Corner Q)) : Prop :=
  (univ.filter fun ρ : {a // a ∈ D} => rowSide t PS ρ.1 = true).card =
    (univ.filter fun a : {a // a ∈ D} => colSide t a.1 = true).card

instance (t : Fin Q) (D PS : Finset (Corner Q)) : Decidable (Balanced t D PS) := by
  unfold Balanced
  infer_instance

/-- A permutation of the corners in use that moves to each column a row of the side of this column, and the identity if the
cube is not balanced. -/
noncomputable def pairOf (t : Fin Q) (D PS : Finset (Corner Q)) : Equiv.Perm {a // a ∈ D} :=
  if hB : Balanced t D PS then (exists_perm_sides _ _ hB).choose else 1

theorem rowSide_pairOf {t : Fin Q} {D PS : Finset (Corner Q)} (hB : Balanced t D PS) (a : {a // a ∈ D}) :
    rowSide t PS (pairOf t D PS a).1 = colSide t a.1 := by
  unfold pairOf
  rw [dif_pos hB]
  exact (exists_perm_sides _ _ hB).choose_spec a

/-- The sign of the cube: the sign of `pairOf` if the cube is balanced, and `0` if not. It depends only on the digit, the
corners in use and the corners of `S`. -/
noncomputable def cubeSign (t : Fin Q) (D PS : Finset (Corner Q)) : ℤ :=
  if Balanced t D PS then ((Equiv.Perm.sign (pairOf t D PS) : ℤˣ) : ℤ) else 0

/-- The matrix of the side `b`: the columns of the side `b`, with the rows that `pairOf` moves to them. -/
noncomputable def sideMat (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) (xv yv : Corner Q → ℚ)
    (b : Bool) :
    Matrix {a : {a // a ∈ D} // colSide t a.1 = b} {a : {a // a ∈ D} // colSide t a.1 = b} (Pz Q) :=
  ((cubeMat κ R t D PT PS xv yv).submatrix (pairOf t D PS) id).toSquareBlock (fun a => colSide t a.1) b

/-- **The side.** The determinant of the matrix of the side `b`, a polynomial in `z`, and `0` if the cube is not balanced. It is a
function of the digit, the corners and the bits at the corners only. -/
noncomputable def sidePoly (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) (xv yv : Corner Q → ℚ)
    (b : Bool) : Pz Q :=
  if Balanced t D PS then (sideMat κ R t D PT PS xv yv b).det else 0

/-- **The determinant of a cube.** It is the sign of the cube times the two sides. -/
theorem det_cubeMat (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) (xv yv : Corner Q → ℚ) :
    (cubeMat κ R t D PT PS xv yv).det =
      C ((cubeSign t D PS : ℤ) : ℚ) * ∏ b : Bool, sidePoly κ R t D PT PS xv yv b := by
  classical
  have hN : ∀ ρ a : {a // a ∈ D}, rowSide t PS ρ.1 ≠ colSide t a.1 → cubeMat κ R t D PT PS xv yv ρ a = 0 := by
    intro ρ a hne
    simp only [cubeMat, Matrix.of_apply, cubeCoef_eq_zero κ R PT hne, zero_mul]
  by_cases hB : Balanced t D PS
  · rw [det_eq_sign_mul_sides _ (fun ρ => rowSide t PS ρ.1) (fun a => colSide t a.1) hN (pairOf t D PS)
      (rowSide_pairOf hB)]
    simp only [sidePoly, cubeSign, if_pos hB]
    congr 1
  · rw [det_eq_zero_of_card_ne _ _ _ hN hB]
    simp [cubeSign, hB]

/-- **What a side reads.** The side `b` reads `xv` only on the rows of the side `b`, and `yv` only on the columns of the
side `b`. -/
theorem sidePoly_congr (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) {xv xv' yv yv' : Corner Q → ℚ}
    (b : Bool) (hx : ∀ ρ ∈ D, rowSide t PS ρ = b → xv ρ = xv' ρ) (hy : ∀ a ∈ D, colSide t a = b → yv a = yv' a) :
    sidePoly κ R t D PT PS xv yv b = sidePoly κ R t D PT PS xv' yv' b := by
  unfold sidePoly
  by_cases hB : Balanced t D PS
  · rw [if_pos hB, if_pos hB]
    congr 1
    ext1 a a'
    show cubeCoef κ R t PT PS (pairOf t D PS a.1).1 a'.1.1 *
        C (eqv (xv (pairOf t D PS a.1).1) (yv a'.1.1)) =
      cubeCoef κ R t PT PS (pairOf t D PS a.1).1 a'.1.1 *
        C (eqv (xv' (pairOf t D PS a.1).1) (yv' a'.1.1))
    rw [hx _ (pairOf t D PS a.1).2 ((rowSide_pairOf hB a.1).trans a.2), hy _ a'.1.2 a'.2]
  · rw [if_neg hB, if_neg hB]

/-- The exponents of a side are at most `2 ^ Q`, since a side has at most `2 ^ Q` rows. -/
theorem sidePoly_exp_le (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) (xv yv : Corner Q → ℚ)
    (b : Bool) : ∀ c ∈ (sidePoly κ R t D PT PS xv yv b).support, ∀ v, c v ≤ 2 ^ Q := by
  intro c hc v
  refine (degreeOf_le_iff.mp ?_) c hc
  unfold sidePoly
  split_ifs
  · refine (degreeOf_det_le _ v fun a a' => ?_).trans ?_
    · exact OnePigeonhole.degreeOf_mul_C_le v _ (degreeOf_cubeCoef_le κ R t v PT PS _ _)
    · calc Fintype.card {a : {a // a ∈ D} // colSide t a.1 = b} ≤ Fintype.card {a // a ∈ D} :=
            Fintype.card_subtype_le _
        _ ≤ Fintype.card (Corner Q) := Fintype.card_subtype_le _
        _ = 2 ^ Q := by simp
  · simp

/-! ### The sign on a side -/

/-- The side `b` with the sign of the cube on the side `false`. This polynomial needs no separate computation of a sign. -/
noncomputable def sideS (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) (xv yv : Corner Q → ℚ)
    (b : Bool) : Pz Q :=
  C (if b then 1 else ((cubeSign t D PS : ℤ) : ℚ)) * sidePoly κ R t D PT PS xv yv b

/-- The two sides with the sign are the sign of the cube times the two sides. -/
theorem prod_sideS (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) (xv yv : Corner Q → ℚ) :
    ∏ b : Bool, sideS κ R t D PT PS xv yv b =
      C ((cubeSign t D PS : ℤ) : ℚ) * ∏ b : Bool, sidePoly κ R t D PT PS xv yv b := by
  simp only [sideS, Fintype.prod_bool, if_true, Bool.false_eq_true, if_false, map_one]
  ring

/-- The side with the sign reads the same bits as the side. -/
theorem sideS_congr (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) {xv xv' yv yv' : Corner Q → ℚ}
    (b : Bool) (hx : ∀ ρ ∈ D, rowSide t PS ρ = b → xv ρ = xv' ρ) (hy : ∀ a ∈ D, colSide t a = b → yv a = yv' a) :
    sideS κ R t D PT PS xv yv b = sideS κ R t D PT PS xv' yv' b := by
  rw [sideS, sideS, sidePoly_congr κ R t D PT PS b hx hy]

/-- The exponents of the side with the sign are at most `2 ^ Q`. -/
theorem sideS_exp_le (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (D PT PS : Finset (Corner Q)) (xv yv : Corner Q → ℚ)
    (b : Bool) : ∀ c ∈ (sideS κ R t D PT PS xv yv b).support, ∀ v, c v ≤ 2 ^ Q := by
  intro c hc v
  refine (degreeOf_le_iff.mp ?_) c hc
  refine degreeOf_C_mul_le' v _ ((degreeOf_le_iff.mpr ?_))
  exact fun c' hc' => sidePoly_exp_le κ R t D PT PS xv yv b c' hc' v

end OnePigeonhole
