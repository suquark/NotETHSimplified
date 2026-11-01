import OnePigeonhole.Pseudo.Helpers
import OnePigeonhole.Net

/-!
# The sides as numbers, and the formula with integers

Equation (5) of `papers/one-pigeonhole/proof.tex` on the grid (`net_decomp_masks`), with one common denominator, as a statement in `ℤ`.

* `sideT`: the side of a cube, given by numbers: the digit, the side and five words of `2 ^ Q` bits. These numbers index the literal table.
* `sideZ`: the scaled value of a side at a grid point, as a sum over the box of exponents.
* `fullWord`: the word of `2 ^ Q` bits at the corners of a cube, for an assignment of the wires. `sideT_fullWord`: with these words, `sideT` is
  the side of the cube, with its sign.
* `blockZ`, `letterZ`: the scaled function of a letter, and the summand of a letter.
* `net_int`: the network sum as a formula with these terms. The common denominator is `Wden * D ^ (2 * #keys)`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo MvPolynomial

variable {Q L h M : ℕ}

/-! ### Scaling -/

/-- `D * q` is an integer of absolute value at most `A`. -/
def IsScaled (D : ℕ) (A : ℝ) (q : ℚ) : Prop := ∃ z : ℤ, (D : ℚ) * q = z ∧ |(z : ℝ)| ≤ A

/-- The integer `D * q`, when `D * q` is an integer. -/
def scaled (D : ℕ) (q : ℚ) : ℤ := ((D : ℚ) * q).num

theorem scaled_cast {D : ℕ} {A : ℝ} {q : ℚ} (h : IsScaled D A q) : (scaled D q : ℚ) = D * q := by
  obtain ⟨z, hz, -⟩ := h
  unfold scaled
  rw [hz]
  simp

/-- A finite family of rationals has a common denominator and a common bound. -/
theorem exists_common {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    ∃ (D : ℕ) (A : ℝ), 1 ≤ D ∧ ∀ i, IsScaled D A (f i) := by
  classical
  let D : ℕ := ∏ i, (f i).den
  have hD : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => (f i).den_ne_zero)
  have hint : ∀ i, ∃ z : ℤ, (D : ℚ) * f i = z := by
    intro i
    obtain ⟨w, hw⟩ : (f i).den ∣ D := dvd_prod_of_mem _ (mem_univ i)
    refine ⟨(f i).num * w, ?_⟩
    have hq : ((f i).den : ℚ) * f i = (f i).num := Rat.den_mul_eq_num _
    rw [hw]
    push_cast
    calc ((f i).den : ℚ) * w * f i = (((f i).den : ℚ) * f i) * w := by ring
      _ = _ := by rw [hq]
  choose z hz using hint
  refine ⟨D, ∑ i, |(z i : ℝ)|, hD, fun i => ⟨z i, hz i, ?_⟩⟩
  exact single_le_sum (f := fun i => |(z i : ℝ)|) (fun _ _ => abs_nonneg _) (mem_univ i)

/-! ### One side, given by numbers -/

/-- **The side of a cube, given by numbers.** The word `Dw` holds the corners in use, `PTw`, `PSw` the corners of `T`, `S`, and `xw`, `yw`
the bits at the corners. -/
noncomputable def sideT (R : ℕ) (t : Fin Q) (Dw : ℕ) (b : Bool) (PTw PSw xw yw : ℕ) : Pz Q :=
  sideS (kappa Q R) R t (posSet Dw) (posSet PTw) (posSet PSw) (bitVal xw) (bitVal yw) b

theorem sideT_exp_le (R : ℕ) (t : Fin Q) (Dw : ℕ) (b : Bool) (PTw PSw xw yw : ℕ) :
    ∀ c ∈ (sideT R t Dw b PTw PSw xw yw).support, ∀ i, c i ≤ 2 ^ Q :=
  sideS_exp_le _ R t _ _ _ _ _ b

/-- The scaled coefficient of a side at an exponent vector. -/
noncomputable def coefZ (D R : ℕ) (t : Fin Q) (Dw : ℕ) (b : Bool) (PTw PSw xw yw : ℕ) (e : Box Q) : ℤ :=
  scaled D (coeff (expOf e) (sideT R t Dw b PTw PSw xw yw))

/-- The scaled value of a side at a grid point. -/
noncomputable def sideZ (D R : ℕ) (t : Fin Q) (Dw : ℕ) (b : Bool) (PTw PSw xw yw : ℕ) (y : Fin Q → ℕ) : ℤ :=
  ∑ e : Box Q, coefZ D R t Dw b PTw PSw xw yw e * ∏ i, (y i : ℤ) ^ (e i : ℕ)

/-- All the coefficients of the sides are integers after scaling by `D`. -/
def SideScaled (D R Q : ℕ) : Prop :=
  ∃ A : ℝ, ∀ (t : Fin Q) (Dw : ℕ) (b : Bool) (PTw PSw xw yw : ℕ) (e : Box Q),
    IsScaled D A (coeff (expOf e) (sideT R t Dw b PTw PSw xw yw))

theorem sideZ_cast {D R : ℕ} (hD : SideScaled D R Q) (t : Fin Q) (Dw : ℕ) (b : Bool) (PTw PSw xw yw : ℕ)
    (y : Fin Q → ℕ) :
    ((sideZ D R t Dw b PTw PSw xw yw y : ℤ) : ℚ) =
      D * eval (fun i => (y i : ℚ)) (sideT R t Dw b PTw PSw xw yw) := by
  obtain ⟨A, hA⟩ := hD
  rw [eval_eq_box _ (sideT_exp_le R t Dw b PTw PSw xw yw), Finset.mul_sum]
  unfold sideZ
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold coefZ
  rw [scaled_cast (hA t Dw b PTw PSw xw yw e)]
  ring

/-! ### The words at the corners of a cube -/

/-- The word of the corners of the cube of `k` that hold a wire with the bit `true` of `f`. The number of a corner `a` is `Enum.mask a`. -/
noncomputable def fullWord (W : Wires Q L h M) (k : Key Q L h) (f : Fin M → Bool) : ℕ :=
  patWord (univ.filter fun a : Corner Q => ∃ i, W.c i = corner k a ∧ f i = true)

/-- The assignment of the membership in `Z`. -/
def memB (Z : Finset (Fin M)) (i : Fin M) : Bool := decide (i ∈ Z)

/-- The assignment `x̃` on bits: the bit of `U` on the rows of `S`, and the bit of `x` on the others. -/
def xtB (S U : Finset (Fin M)) (x : Fin M → Bool) (i : Fin M) : Bool := if i ∈ S then decide (i ∈ U) else x i

theorem posSet_fullWord (W : Wires Q L h M) {k : Key Q L h} (hk : IsKey k) (Z : Finset (Fin M)) :
    posSet (fullWord W k (memB Z)) = W.cornersOf k Z := by
  rw [fullWord, posSet_patWord]
  ext a
  simp only [mem_filter, mem_univ, true_and, Wires.cornersOf, mem_image, memB, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hc, hZ⟩
    obtain ⟨h1, h2⟩ := (W.key_F_iff_c_eq hk i a).mpr hc
    exact ⟨i, ⟨hZ, h1⟩, h2⟩
  · rintro ⟨i, ⟨hZ, h1⟩, h2⟩
    exact ⟨i, (W.key_F_iff_c_eq hk i a).mp ⟨h1, h2⟩, hZ⟩

theorem posSet_fullWord_used (W : Wires Q L h M) {k : Key Q L h} (hk : IsKey k) :
    posSet (fullWord W k fun _ => true) = W.used k := by
  have e : (fun _ : Fin M => true) = memB univ := by
    funext i
    simp [memB]
  rw [e, posSet_fullWord W hk]
  rfl

/-- The bits of `fullWord` are the values at the corners. -/
theorem bitVal_fullWord (W : Wires Q L h M) {k : Key Q L h} (hk : IsKey k) (f : Fin M → Bool) :
    bitVal (fullWord W k f) = W.atCorner k fun i => bit (f i) := by
  funext a
  have hmem : (fullWord W k f).testBit (Enum.mask a) = true ↔ ∃ i, W.c i = corner k a ∧ f i = true := by
    unfold fullWord
    rw [testBit_patWord]
    simp
  unfold bitVal Wires.atCorner
  simp only [W.key_F_iff_c_eq hk]
  by_cases hex : ∃ i0, W.c i0 = corner k a
  · obtain ⟨i0, h0⟩ := hex
    rw [Finset.sum_eq_single i0 (fun i _ hne => if_neg fun hc => hne (W.c_inj (hc.trans h0.symm)))
      (fun h1 => absurd (mem_univ i0) h1), if_pos h0]
    cases hf : f i0
    · have : ¬ (fullWord W k f).testBit (Enum.mask a) = true := by
        rw [hmem]
        rintro ⟨i, hc, hi⟩
        rw [W.c_inj (hc.trans h0.symm), hf] at hi
        exact Bool.noConfusion hi
      rw [if_neg this]
      simp [bit]
    · rw [if_pos (hmem.mpr ⟨i0, h0, hf⟩)]
      simp [bit]
  · have : ¬ (fullWord W k f).testBit (Enum.mask a) = true := by
      rw [hmem]
      rintro ⟨i, hc, -⟩
      exact hex ⟨i, hc⟩
    rw [if_neg this, Finset.sum_eq_zero fun i _ => if_neg fun hc => hex ⟨i, hc⟩]

theorem xTilde_bit (S U : Finset (Fin M)) (x : Fin M → Bool) :
    xTilde S U (fun i => bit (x i)) = fun i => bit (xtB S U x i) := by
  funext i
  unfold xTilde xiOf xtB
  by_cases hS : i ∈ S
  · by_cases hU : i ∈ U <;> simp [hS, hU, bit]
  · simp [hS]

/-- **With the words of the wires, `sideT` is the side of the cube, with its sign.** -/
theorem sideT_fullWord (W : Wires Q L h M) (R : ℕ) (t : Fin Q) (T S U : Finset (Fin M)) (x y : Fin M → Bool)
    {k : Key Q L h} (hk : IsKey k) (b : Bool) :
    sideT R t (fullWord W k fun _ => true) b (fullWord W k (memB T)) (fullWord W k (memB S))
        (fullWord W k (xtB S U x)) (fullWord W k y) =
      sideOfS W (kappa Q R) R t T S U (fun i => bit (x i)) (fun j => bit (y j)) k b := by
  unfold sideT sideOfS
  rw [posSet_fullWord_used W hk, posSet_fullWord W hk, posSet_fullWord W hk, bitVal_fullWord W hk,
    bitVal_fullWord W hk, xTilde_bit]

/-! ### One letter -/

/-- The scaled side `b` of the cube of `k`. -/
noncomputable def sideK (D R : ℕ) (W : Wires Q L h M) (t : Fin Q) (p : Fin Q → ℕ) (T S U : Finset (Fin M))
    (x y : Fin M → Bool) (k : Key Q L h) (b : Bool) : ℤ :=
  sideZ D R t (fullWord W k fun _ => true) b (fullWord W k (memB T)) (fullWord W k (memB S))
    (fullWord W k (xtB S U x)) (fullWord W k y) p

/-- The scaled function of the letter `g`: the tests of the rows of `S` with this letter, times the scaled sides with this letter. -/
noncomputable def blockZ (D R : ℕ) (W : Wires Q L h M) (t : Fin Q) (p : Fin Q → ℕ) (T S U : Finset (Fin M))
    (g : Fin L) (x y : Fin M → Bool) : ℤ :=
  (∏ i ∈ S.filter (fun i => W.tw i t = g), if x i = decide (i ∈ U) then 1 else 0) *
    ∏ k ∈ keys Q L h, ∏ b : Bool, if letter k t b = g then sideK D R W t p T S U x y k b else 1

/-- The number of sides with the letter `g` at the digit `t`. -/
def sidesOf (Q L h : ℕ) (t : Fin Q) (g : Fin L) : ℕ :=
  ∑ k ∈ keys Q L h, ∑ b : Bool, if letter k t b = g then 1 else 0

theorem sum_sidesOf (Q L h : ℕ) (t : Fin Q) : ∑ g : Fin L, sidesOf Q L h t g = 2 * (keys Q L h).card := by
  classical
  unfold sidesOf
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp

theorem eqv_xiOf (a : Bool) (U : Finset (Fin M)) (i : Fin M) :
    eqv (bit a) (xiOf U i) = if a = decide (i ∈ U) then 1 else 0 := by
  have e : xiOf U i = bit (decide (i ∈ U)) := by simp [xiOf, bit]
  rw [e, eqv_bit]
  by_cases hU : i ∈ U <;> cases a <;> simp [hU]

/-- The scaled function of a letter, in the rationals, is a power of `D` times the function `blockS`. -/
theorem blockZ_cast {D R : ℕ} (hD : SideScaled D R Q) (W : Wires Q L h M) (t : Fin Q) (p : Fin Q → ℕ)
    (T S U : Finset (Fin M)) (g : Fin L) (x y : Fin M → Bool) :
    ((blockZ D R W t p T S U g x y : ℤ) : ℚ) =
      (D : ℚ) ^ sidesOf Q L h t g *
        blockS W (kappa Q R) R t (fun i => (p i : ℚ)) T S U g (fun i => bit (x i)) (fun j => bit (y j)) := by
  classical
  unfold blockZ blockS sidesOf
  push_cast
  rw [← Finset.prod_pow_eq_pow_sum]
  have h1 : ∀ i ∈ S.filter (fun i => W.tw i t = g), ((if x i = decide (i ∈ U) then 1 else 0 : ℚ)) =
      eqv (bit (x i)) (xiOf U i) := fun i _ => (eqv_xiOf _ _ _).symm
  rw [Finset.prod_congr rfl h1, mul_left_comm]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases hb : letter k t b = g
  · simp only [hb, if_true, pow_one]
    unfold sideK
    rw [sideZ_cast hD, sideT_fullWord W R t T S U x y (mem_keys.mp hk) b]
  · simp [hb]

/-! ### The network -/

section Net

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The summand of the letter `g`, for an assignment `v` of the bits of `g`, as an integer. -/
noncomputable def letterZ (D R : ℕ) (W : Wires Q L h M) (tail head : Fin M → V) (wd : V → Fin Q → Fin L)
    (φ : (α : V) → (Inc tail head α → Bool) → ℤ) (t : Fin Q) (p : Fin Q → ℕ) (T S U : Finset (Fin M)) (g : Fin L)
    (v : BlockBits wd tail head t g → Bool) : ℤ :=
  blockZ D R W t p T S U g (blockExt wd tail head t g v ∘ Sum.inl) (blockExt wd tail head t g v ∘ Sum.inr) *
    ∏ α ∈ univ.filter (fun α => wd α t = g),
      φ α (read tail head α (blockExt wd tail head t g v ∘ Sum.inl) (blockExt wd tail head t g v ∘ Sum.inr))

theorem letterZ_cast {D R : ℕ} (hD : SideScaled D R Q) (W : Wires Q L h M) (tail head : Fin M → V)
    (wd : V → Fin Q → Fin L) (φ : (α : V) → (Inc tail head α → Bool) → ℤ) (t : Fin Q) (p : Fin Q → ℕ)
    (T S U : Finset (Fin M)) (g : Fin L) (v : BlockBits wd tail head t g → Bool) :
    ((letterZ D R W tail head wd φ t p T S U g v : ℤ) : ℚ) =
      (D : ℚ) ^ sidesOf Q L h t g *
        letterTerm tail head wd (fun α u => (φ α u : ℚ)) t g
          (blockS W (kappa Q R) R t (fun i => (p i : ℚ)) T S U g) v := by
  unfold letterZ letterTerm
  push_cast
  rw [blockZ_cast hD]
  simp only [Function.comp]
  ring

/-- The test of the masks with the sign: `|T| ≤ r` and `U ⊆ S`. -/
def cTest (r : ℕ) (T S U : Finset (Fin M)) : ℤ := if T.card ≤ r ∧ U ⊆ S then (-1) ^ T.card else 0

theorem cTest_cast (r : ℕ) (T S U : Finset (Fin M)) :
    ((cTest r T S U : ℤ) : ℚ) = if T.card ≤ r ∧ U ⊆ S then (-1) ^ T.card else 0 := by
  unfold cTest
  split_ifs <;> simp

/-- **The formula with integers.** The common denominator is `Wden * D ^ (2 * #keys)`: each side of each cube has one letter, and it
contributes one factor of `D`. -/
theorem net_int {W : Wires Q L h M} {tail head : Fin M → V} {wd : V → Fin Q → Fin L} (hW : OnNodes W tail head wd)
    {D R r J : ℕ} (hD : SideScaled D R Q) (hr : 2 * rankBound Q L h R ≤ r) (hJ : M * R + r * Q < Q * J)
    (Wden : ℕ) (w : Fin Q → (Fin Q → Fin (M + 1)) → ℤ)
    (hw : ∀ t p, (w t p : ℚ) = Wden * digitWeight (k := ℚ) M J t p)
    (φ : (α : V) → (Inc tail head α → Bool) → ℤ) :
    ((Wden * D ^ (2 * (keys Q L h).card) : ℕ) : ℤ) * ∑ z : Fin M → Bool, ∏ α, φ α (fun e => z e.1) =
      ∑ t, ∑ p : Fin Q → Fin (M + 1), ∑ T ∈ fewW M J, ∑ S ∈ fewW M J, ∑ U ∈ fewW M J,
        w t p * cTest r T S U * ∏ g, ∑ v : BlockBits wd tail head t g → Bool,
          letterZ D R W tail head wd φ t (fun i => (p i : ℕ)) T S U g v := by
  classical
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [net_decomp_masks hW hr hJ (fun α u => (φ α u : ℚ)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [hw, cTest_cast]
  have hprod : (∏ g, ∑ v : BlockBits wd tail head t g → Bool,
      ((letterZ D R W tail head wd φ t (fun i => (p i : ℕ)) T S U g v : ℤ) : ℚ)) =
      (D : ℚ) ^ (2 * (keys Q L h).card) *
        ∏ g, ∑ v : BlockBits wd tail head t g → Bool,
          letterTerm tail head wd (fun α u => (φ α u : ℚ)) t g
            (blockS W (kappa Q R) R t (fun i => gridPt (k := ℚ) M (p i)) T S U g) v := by
    rw [← sum_sidesOf Q L h t, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [letterZ_cast hD]
    rfl
  rw [hprod]
  ring

end Net

end OnePigeonhole.Pseudo
