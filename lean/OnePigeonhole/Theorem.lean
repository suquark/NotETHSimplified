import OnePigeonhole.Blocks

/-!
# The decomposition

Section 4 of `papers/one-pigeonhole/proof.tex`: `∏ j, [x_j = y_j]` as a fixed combination of products over the letters of a digit,
before the sum over the bits in equation (5). The text factors `det H^ξ` by letters. Here it is factored further, by a cube and a
side of the digit, so that each factor is a determinant of order at most `2 ^ Q`.

The numbers `Q`, `R`, `L`, `h`, `r`, `J` are general, with the hypotheses `2 * rankBound Q L h R ≤ r` and
`M * R + r * Q < Q * J`. In the text, `Q = m ^ 4`, `R = m ^ 3`, and `|T| ≤ r`, `|S| ≤ 2 r`. All identities hold for all rationals `x`, `y`.

* `sideOf`: the side `b` of a cube, which is `sidePoly` of `Cube.lean` with the corner data of the wires.
* `signOf`: the sign `sgn(t, S)`, the product of `cubeSign` over the cubes. It is `0` if `S` is not balanced.
* `psiZ`: the polynomial of the letter `g`: the tests `[x_i = ξ_i]` of the rows of `S` with `s_i = g`, times the sides with the letter `g`.
  With the clause factors, this is `Ψ_g` of the text.
* `blockF`: the value of `psiZ` at a point. `sideOfS`, `blockS`: the same with `sideS`, so each sign of a cube sits in one letter.
* `ReadsLetter`, `psiZ_congr`, `blockF_reads`, `blockS_reads`: these functions read only the bits of the letter `g`.
* `det_decomp_sumT`: the form with `Sum_t` and the products over the letters, as in equation (5).
* `det_decomp_cubes`: the form on the grid, with a product over the cubes of the sign and the two sides.
* `det_decomp`: the form on the grid, with `sgn(t, S)` and a product over the letters of `blockF`.
* `det_decomp_masks`: the form on the grid, with one range of masks and a product over the letters of `blockS`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole

open Finset TransposeBase MvPolynomial

variable {Q L h M : ℕ}

/-! ### The factors -/

/-- The side `b` of the cube of `k`, with the numbers `ξ` of `U` for the bits of the rows of `S`. -/
noncomputable def sideOf (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (T S U : Finset (Fin M))
    (x y : Fin M → ℚ) (k : Key Q L h) (b : Bool) : Pz Q :=
  sidePoly κ R t (W.used k) (W.cornersOf k T) (W.cornersOf k S)
    (W.atCorner k (xTilde S U x)) (W.atCorner k y) b

/-- The sign `sgn(t, S)`: the product over the cubes of `cubeSign`. It is `0` if `S` is not balanced on some cube. -/
noncomputable def signOf (W : Wires Q L h M) (t : Fin Q) (S : Finset (Fin M)) : ℤ :=
  ∏ k ∈ keys Q L h, cubeSign t (W.used k) (W.cornersOf k S)

/-- The polynomial of the letter `g`: the tests `[x_i = ξ_i]` of the rows `i ∈ S` with `s_i = g`, times the sides with the
letter `g`. -/
noncomputable def psiZ (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (T S U : Finset (Fin M)) (g : Fin L)
    (x y : Fin M → ℚ) : Pz Q :=
  C (∏ i ∈ S.filter (fun i => W.tw i t = g), eqv (x i) (xiOf U i)) *
    ∏ k ∈ keys Q L h, ∏ b : Bool, if letter k t b = g then sideOf W κ R t T S U x y k b else 1

/-- The block function of the letter `g` at the point `pt`: the value of `psiZ`. -/
noncomputable def blockF (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (pt : Fin Q → ℚ)
    (T S U : Finset (Fin M)) (g : Fin L) (x y : Fin M → ℚ) : ℚ :=
  (∏ i ∈ S.filter (fun i => W.tw i t = g), eqv (x i) (xiOf U i)) *
    ∏ k ∈ keys Q L h, ∏ b : Bool, if letter k t b = g then eval pt (sideOf W κ R t T S U x y k b) else 1

/-- The side `b` of the cube of `k`, with the sign of the cube on the side `false`. -/
noncomputable def sideOfS (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (T S U : Finset (Fin M))
    (x y : Fin M → ℚ) (k : Key Q L h) (b : Bool) : Pz Q :=
  sideS κ R t (W.used k) (W.cornersOf k T) (W.cornersOf k S)
    (W.atCorner k (xTilde S U x)) (W.atCorner k y) b

/-- The block function of the letter `g` at the point `pt`, with the signs of the cubes in the sides. -/
noncomputable def blockS (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (pt : Fin Q → ℚ)
    (T S U : Finset (Fin M)) (g : Fin L) (x y : Fin M → ℚ) : ℚ :=
  (∏ i ∈ S.filter (fun i => W.tw i t = g), eqv (x i) (xiOf U i)) *
    ∏ k ∈ keys Q L h, ∏ b : Bool, if letter k t b = g then eval pt (sideOfS W κ R t T S U x y k b) else 1

theorem eval_psiZ (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (pt : Fin Q → ℚ)
    (T S U : Finset (Fin M)) (g : Fin L) (x y : Fin M → ℚ) :
    eval pt (psiZ W κ R t T S U g x y) = blockF W κ R t pt T S U g x y := by
  simp only [psiZ, blockF, map_mul, eval_C, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun b _ => ?_
  split_ifs <;> simp

/-! ### What the factors read -/

/-- `Φ` reads only the bits of the letter `g` at the digit `t`: the `x i` with `W.tw i t = g`, and the `y j` with
`W.hw j t = g`. -/
def ReadsLetter (W : Wires Q L h M) (t : Fin Q) (g : Fin L) {β : Type*} (Φ : (Fin M → ℚ) → (Fin M → ℚ) → β) : Prop :=
  ∀ x x' y y', (∀ i, W.tw i t = g → x i = x' i) → (∀ j, W.hw j t = g → y j = y' j) → Φ x y = Φ x' y'

/-- The bits at the corners that a side with the letter `g` reads are bits of `g`. -/
theorem side_bits_of_letter (W : Wires Q L h M) (t : Fin Q) (S U : Finset (Fin M))
    {x x' y y' : Fin M → ℚ} {k : Key Q L h} {b : Bool} {g : Fin L} (hg : letter k t b = g)
    (hx : ∀ i, W.tw i t = g → x i = x' i) (hy : ∀ j, W.hw j t = g → y j = y' j) :
    (∀ ρ ∈ W.used k, rowSide t (W.cornersOf k S) ρ = b →
      W.atCorner k (xTilde S U x) ρ = W.atCorner k (xTilde S U x') ρ) ∧
    (∀ a ∈ W.used k, colSide t a = b → W.atCorner k y a = W.atCorner k y' a) := by
  refine ⟨fun ρ hρ hside => ?_, fun a ha hside => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := W.exists_of_mem_used hρ
    rw [W.atCorner_F hi, W.atCorner_F hi]
    unfold xTilde
    by_cases hS : i ∈ S
    · rw [if_pos hS, if_pos hS]
    · rw [if_neg hS, if_neg hS]
      apply hx
      have h1 := letter_rowSide W t S hi
      rw [hside, hg, if_neg hS] at h1
      exact h1.symm
  · obtain ⟨j, hj, rfl⟩ := W.exists_of_mem_used ha
    rw [W.atCorner_F hj, W.atCorner_F hj]
    apply hy
    have h1 := letter_colSide W t hj
    rw [hside, hg] at h1
    exact h1.symm

/-- A side with the letter `g` reads only the bits of the letter `g`. -/
theorem sideOf_congr (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (T S U : Finset (Fin M))
    {x x' y y' : Fin M → ℚ} {k : Key Q L h} {b : Bool} {g : Fin L} (hg : letter k t b = g)
    (hx : ∀ i, W.tw i t = g → x i = x' i) (hy : ∀ j, W.hw j t = g → y j = y' j) :
    sideOf W κ R t T S U x y k b = sideOf W κ R t T S U x' y' k b :=
  sidePoly_congr κ R t _ _ _ b (side_bits_of_letter W t S U hg hx hy).1
    (side_bits_of_letter W t S U hg hx hy).2

/-- **The polynomial of a letter reads only the bits of this letter.** -/
theorem psiZ_congr (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (T S U : Finset (Fin M)) (g : Fin L) :
    ReadsLetter W t g (psiZ W κ R t T S U g) := by
  intro x x' y y' hx hy
  have h1 : (∏ i ∈ S.filter (fun i => W.tw i t = g), eqv (x i) (xiOf U i)) =
      ∏ i ∈ S.filter (fun i => W.tw i t = g), eqv (x' i) (xiOf U i) :=
    Finset.prod_congr rfl fun i hi => by rw [hx i (Finset.mem_filter.mp hi).2]
  have h2 : (∏ k ∈ keys Q L h, ∏ b : Bool, if letter k t b = g then sideOf W κ R t T S U x y k b else 1) =
      ∏ k ∈ keys Q L h, ∏ b : Bool, if letter k t b = g then sideOf W κ R t T S U x' y' k b else 1 := by
    refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun b _ => ?_
    by_cases hg : letter k t b = g
    · rw [if_pos hg, if_pos hg, sideOf_congr W κ R t T S U hg hx hy]
    · rw [if_neg hg, if_neg hg]
  rw [psiZ, psiZ, h1, h2]

/-- **The block function reads only the bits of its letter.** -/
theorem blockF_reads (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (pt : Fin Q → ℚ)
    (T S U : Finset (Fin M)) (g : Fin L) : ReadsLetter W t g (blockF W κ R t pt T S U g) := by
  intro x x' y y' hx hy
  rw [← eval_psiZ, ← eval_psiZ, psiZ_congr W κ R t T S U g x x' y y' hx hy]

/-- **The block function with the signs reads only the bits of its letter.** -/
theorem blockS_reads (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (pt : Fin Q → ℚ)
    (T S U : Finset (Fin M)) (g : Fin L) : ReadsLetter W t g (blockS W κ R t pt T S U g) := by
  intro x x' y y' hx hy
  have h1 : (∏ i ∈ S.filter (fun i => W.tw i t = g), eqv (x i) (xiOf U i)) =
      ∏ i ∈ S.filter (fun i => W.tw i t = g), eqv (x' i) (xiOf U i) :=
    Finset.prod_congr rfl fun i hi => by rw [hx i (Finset.mem_filter.mp hi).2]
  have h2 : (∏ k ∈ keys Q L h, ∏ b : Bool,
        if letter k t b = g then eval pt (sideOfS W κ R t T S U x y k b) else 1) =
      ∏ k ∈ keys Q L h, ∏ b : Bool,
        if letter k t b = g then eval pt (sideOfS W κ R t T S U x' y' k b) else 1 := by
    refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun b _ => ?_
    by_cases hg : letter k t b = g
    · have hs : sideOfS W κ R t T S U x y k b = sideOfS W κ R t T S U x' y' k b :=
        sideS_congr κ R t _ _ _ b (side_bits_of_letter W t S U hg hx hy).1
          (side_bits_of_letter W t S U hg hx hy).2
      rw [if_pos hg, if_pos hg, hs]
    · rw [if_neg hg, if_neg hg]
  rw [blockS, blockS, h1, h2]

/-! ### The products -/

/-- The product over the letters of the factors with this letter is the product of all factors, since each side of each cube has
one letter. -/
theorem prod_letters {β : Type*} [CommMonoid β] (t : Fin Q) (f : Key Q L h → Bool → β) :
    ∏ g : Fin L, ∏ k ∈ keys Q L h, ∏ b : Bool, (if letter k t b = g then f k b else 1) =
      ∏ k ∈ keys Q L h, ∏ b : Bool, f k b := by
  classical
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Finset.prod_ite_eq]
  simp

/-- The determinant of `H^ξ` is the sign `sgn(t, S)` times the sides of all cubes. -/
theorem det_Hz_xTilde (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S U : Finset (Fin M)) (x y : Fin M → ℚ) :
    (Hz W κ R T t S (xTilde S U x) y).det =
      ∏ k ∈ keys Q L h, (C ((cubeSign t (W.used k) (W.cornersOf k S) : ℤ) : ℚ) *
        ∏ b : Bool, sideOf W κ R t T S U x y k b) := by
  rw [det_Hz_eq_prod]
  exact Finset.prod_congr rfl fun k _ => det_cubeMat κ R t _ _ _ _ _

/-- **The factorization by letters.** The determinant of `H^ξ` is `sgn(t, S)` times, over the letters `g`, the product of the
sides with the letter `g`. This product stands for `det H^ξ_g` of Section 4, up to a sign. -/
theorem det_Hz_xTilde_letters (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S U : Finset (Fin M)) (x y : Fin M → ℚ) :
    (Hz W κ R T t S (xTilde S U x) y).det =
      C ((signOf W t S : ℤ) : ℚ) *
        ∏ g : Fin L, ∏ k ∈ keys Q L h, ∏ b : Bool,
          if letter k t b = g then sideOf W κ R t T S U x y k b else 1 := by
  rw [det_Hz_xTilde, Finset.prod_mul_distrib, signOf, prod_letters, Int.cast_prod, map_prod]

/-- The product of the polynomials of the letters is the product of all tests and all sides. -/
theorem prod_psiZ (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (T S U : Finset (Fin M)) (x y : Fin M → ℚ) :
    ∏ g : Fin L, psiZ W κ R t T S U g x y =
      C (∏ i ∈ S, eqv (x i) (xiOf U i)) *
        ∏ g : Fin L, ∏ k ∈ keys Q L h, ∏ b : Bool,
          if letter k t b = g then sideOf W κ R t T S U x y k b else 1 := by
  classical
  unfold psiZ
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_fiberwise]

/-- `det H_{T,t,S}` is the sum over the numbers `ξ` of `sgn(t, S)` times the product of the polynomials of the letters. -/
theorem det_Hz_eq_sum_psiZ (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (x y : Fin M → ℚ) :
    (Hz W κ R T t S x y).det =
      ∑ U ∈ S.powerset, C ((signOf W t S : ℤ) : ℚ) * ∏ g : Fin L, psiZ W κ R t T S U g x y := by
  rw [det_Hz_eq_sum_U]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [det_Hz_xTilde_letters, prod_psiZ]
  ring

/-- The value of `det H_{T,t,S}` at a point, as a sum over the numbers `ξ` of the tests, the signs and the sides of all cubes. -/
theorem eval_det_Hz (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (T : Finset (Fin M)) (t : Fin Q)
    (S : Finset (Fin M)) (pt : Fin Q → ℚ) (x y : Fin M → ℚ) :
    eval pt (Hz W κ R T t S x y).det =
      ∑ U ∈ S.powerset, (∏ i ∈ S, eqv (x i) (xiOf U i)) *
        ∏ k ∈ keys Q L h, (((cubeSign t (W.used k) (W.cornersOf k S) : ℤ) : ℚ) *
          ∏ b : Bool, eval pt (sideOf W κ R t T S U x y k b)) := by
  rw [det_Hz_eq_sum_U, map_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [det_Hz_xTilde]
  simp only [map_mul, eval_C, map_prod]

/-- The product of the block functions over the letters is the product of all tests and all sides. -/
theorem prod_blockF (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (pt : Fin Q → ℚ)
    (T S U : Finset (Fin M)) (x y : Fin M → ℚ) :
    ∏ g : Fin L, blockF W κ R t pt T S U g x y =
      (∏ i ∈ S, eqv (x i) (xiOf U i)) *
        ∏ k ∈ keys Q L h, ∏ b : Bool, eval pt (sideOf W κ R t T S U x y k b) := by
  classical
  unfold blockF
  rw [Finset.prod_mul_distrib, Finset.prod_fiberwise, prod_letters]

/-- The product over the letters of the block functions with the signs is `sgn(t, S)` times the product of the block functions. -/
theorem prod_blockS (W : Wires Q L h M) (κ : ℕ → ℚ) (R : ℕ) (t : Fin Q) (pt : Fin Q → ℚ)
    (T S U : Finset (Fin M)) (x y : Fin M → ℚ) :
    ∏ g : Fin L, blockS W κ R t pt T S U g x y =
      ((signOf W t S : ℤ) : ℚ) * ∏ g : Fin L, blockF W κ R t pt T S U g x y := by
  classical
  have hk : ∀ k ∈ keys Q L h, ∏ b : Bool, eval pt (sideOfS W κ R t T S U x y k b) =
      ((cubeSign t (W.used k) (W.cornersOf k S) : ℤ) : ℚ) *
        ∏ b : Bool, eval pt (sideOf W κ R t T S U x y k b) := by
    intro k _
    have h1 := prod_sideS κ R t (W.used k) (W.cornersOf k T) (W.cornersOf k S)
      (W.atCorner k (xTilde S U x)) (W.atCorner k y)
    have h2 := congrArg (eval pt) h1
    simp only [sideOfS, sideOf]
    simpa only [map_mul, map_prod, eval_C] using h2
  rw [prod_blockF]
  unfold blockS
  rw [Finset.prod_mul_distrib, Finset.prod_fiberwise, prod_letters, Finset.prod_congr rfl hk,
    Finset.prod_mul_distrib, signOf, Int.cast_prod]
  ring

/-- `Sum_t` takes out a constant factor. -/
theorem sumT_C_mul (J : ℕ) (t : Fin Q) (a : ℚ) (f : Pz Q) : sumT J t (C a * f) = a * sumT J t f := by
  have hsub : (C a * f).support ⊆ f.support := by
    intro c hc
    rw [mem_support_iff, coeff_C_mul] at hc
    exact mem_support_iff.mpr (right_ne_zero_of_mul hc)
  rw [sumT_eq_of_subset hsub, sumT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coeff_C_mul]
  split_ifs <;> simp

/-! ### The decomposition -/

/-- **The decomposition with `Sum_t`.** This is the form of equation (5) before the sum over the bits. -/
theorem det_decomp_sumT (W : Wires Q L h M) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (x y : Fin M → ℚ) :
    ∏ j, eqv (x j) (y j) =
      ∑ T ∈ fewW M (r + 1), (-1) ^ T.card *
        ∑ t, ∑ S ∈ fewW M J, ((signOf W t S : ℤ) : ℚ) * ∑ U ∈ S.powerset,
          sumT J t (∏ g : Fin L, psiZ W (kappa Q R) R t T S U g x y) := by
  rw [prod_eqv_eq_sum_sumT W hr hJ x y]
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun S _ => ?_
  rw [det_Hz_eq_sum_psiZ, sumT_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun U _ => sumT_C_mul J t _ _

/-- **The decomposition, by cubes.** For `|T| ≤ r`, a digit `t`, a grid point `p`, `|S| < J` and `U ⊆ S`: the weight, the tests
`[x_i = ξ_i]` for `i ∈ S`, and for each cube its sign and its two sides at the grid point. -/
theorem det_decomp_cubes (W : Wires Q L h M) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (x y : Fin M → ℚ) :
    ∏ j, eqv (x j) (y j) =
      ∑ T ∈ fewW M (r + 1), ∑ t, ∑ p : Fin Q → Fin (M + 1), ∑ S ∈ fewW M J, ∑ U ∈ S.powerset,
        (-1) ^ T.card * digitWeight (k := ℚ) M J t p * (∏ i ∈ S, eqv (x i) (xiOf U i)) *
          ∏ k ∈ keys Q L h, (((cubeSign t (W.used k) (W.cornersOf k S) : ℤ) : ℚ) *
            ∏ b : Bool, eval (fun i => gridPt (k := ℚ) M (p i))
              (sideOf W (kappa Q R) R t T S U x y k b)) := by
  rw [prod_eqv_eq_grid W hr hJ x y]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [eval_det_Hz, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  ring

/-- **The decomposition.** The test of all bits is a fixed combination of products over the letters of block functions, where the
function of the letter `g` reads only the bits of `g` (`blockF_reads`). All the data and the weights come before `x` and `y`. -/
theorem det_decomp (W : Wires Q L h M) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (x y : Fin M → ℚ) :
    ∏ j, eqv (x j) (y j) =
      ∑ T ∈ fewW M (r + 1), ∑ t, ∑ p : Fin Q → Fin (M + 1), ∑ S ∈ fewW M J, ∑ U ∈ S.powerset,
        (-1) ^ T.card * digitWeight (k := ℚ) M J t p * ((signOf W t S : ℤ) : ℚ) *
          ∏ g : Fin L, blockF W (kappa Q R) R t (fun i => gridPt (k := ℚ) M (p i)) T S U g x y := by
  rw [det_decomp_cubes W hr hJ x y]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun t _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun U _ => ?_
  rw [prod_blockF, Finset.prod_mul_distrib, signOf, Int.cast_prod]
  ring

/-- The pigeonhole inequality gives `r < J`. -/
theorem lt_of_pigeon {R r J : ℕ} (hJ : M * R + r * Q < Q * J) : r < J := by
  by_contra hle
  have h1 : Q * J ≤ r * Q := by
    rw [mul_comm]
    exact Nat.mul_le_mul_right Q (not_lt.mp hle)
  omega

/-- **The decomposition, with one range of masks.** The sets `T`, `S`, `U` run over the sets of fewer than `J` rows, and a test
selects `|T| ≤ r` and `U ⊆ S`. The signs of the cubes sit in the sides. -/
theorem det_decomp_masks (W : Wires Q L h M) {R r J : ℕ} (hr : 2 * rankBound Q L h R ≤ r)
    (hJ : M * R + r * Q < Q * J) (x y : Fin M → ℚ) :
    ∏ j, eqv (x j) (y j) =
      ∑ t, ∑ p : Fin Q → Fin (M + 1), ∑ T ∈ fewW M J, ∑ S ∈ fewW M J, ∑ U ∈ fewW M J,
        digitWeight (k := ℚ) M J t p * (if T.card ≤ r ∧ U ⊆ S then (-1) ^ T.card else 0) *
          ∏ g : Fin L, blockS W (kappa Q R) R t (fun i => gridPt (k := ℚ) M (p i)) T S U g x y := by
  classical
  have hrJ : r < J := lt_of_pigeon hJ
  rw [det_decomp W hr hJ x y, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hT : fewW M (r + 1) = (fewW M J).filter fun T => T.card ≤ r := by
    ext T
    simp only [fewW, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hT, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hTr : T.card ≤ r
  · rw [if_pos hTr]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hS' : S.card < J := mem_fewW.mp hS
    have hU : S.powerset = (fewW M J).filter fun U => U ⊆ S := by
      ext U
      simp only [fewW, Finset.mem_powerset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hsub
        exact ⟨(Finset.card_le_card hsub).trans_lt hS', hsub⟩
      · exact fun hU => hU.2
    rw [hU, Finset.sum_filter]
    refine Finset.sum_congr rfl fun U _ => ?_
    by_cases hUS : U ⊆ S
    · rw [if_pos hUS, if_pos (And.intro hTr hUS), prod_blockS]
      ring
    · simp only [if_neg hUS, if_neg (fun hc : T.card ≤ r ∧ U ⊆ S => hUS hc.2), mul_zero, zero_mul]
  · rw [if_neg hTr]
    symm
    refine Finset.sum_eq_zero fun S _ => Finset.sum_eq_zero fun U _ => ?_
    simp only [if_neg (fun hc : T.card ≤ r ∧ U ⊆ S => hTr hc.1), mul_zero, zero_mul]

end OnePigeonhole
