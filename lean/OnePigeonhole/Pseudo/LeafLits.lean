import OnePigeonhole.Pseudo.LeafSetup

/-!
# The literal table exists

For each `m` there are a scale `D`, an offset and one packed word that holds the scaled coefficients of the sides. The side depends on
its numbers only through finite data, so one common denominator exists, and the table depends only on `m`. A sufficient word length is
`C * (K + h + 2 * M + v + fw + 3) ^ 3`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.Pseudo TransposeBase.Pseudo.Code

/-- A scaled coefficient with the offset is a small natural number. -/
theorem scaled_small {D off f : ℕ} {A : ℝ} {q : ℚ} (h : IsScaled D A q) (hoff : A ≤ off) (hf : 2 * off + 1 ≤ 2 ^ f) :
    ((scaled D q + off).toNat : ℤ) = scaled D q + off ∧ (scaled D q + off).toNat < 2 ^ f := by
  have hc := scaled_cast h
  obtain ⟨z, hz, hle⟩ := h
  have hzq : scaled D q = z := by
    have : ((scaled D q : ℤ) : ℚ) = (z : ℚ) := by rw [hc, hz]
    exact_mod_cast this
  rw [hzq]
  have h1 : |(z : ℝ)| ≤ (off : ℝ) := hle.trans hoff
  have h2 : |z| ≤ (off : ℤ) := by exact_mod_cast h1
  have h3 := abs_le.mp h2
  have h4 : 0 ≤ z + off := by omega
  have h5 := Int.toNat_of_nonneg h4
  refine ⟨h5, ?_⟩
  have h6 : ((z + off).toNat : ℤ) ≤ 2 * off := by omega
  have h7 : (z + off).toNat ≤ 2 * off := by exact_mod_cast h6
  omega

theorem sideT_eq_ind {Q : ℕ} (R : ℕ) (t : Fin Q) (Dw : ℕ) (b : Bool) (PTw PSw xw yw : ℕ) :
    sideT R t Dw b PTw PSw xw yw =
      sideS (kappa Q R) R t (posSet Dw) (posSet PTw) (posSet PSw) (indV (posSet xw)) (indV (posSet yw)) b := by
  unfold sideT
  rw [bitVal_eq_ind xw, bitVal_eq_ind yw]

/-- A position in the table determines its parts. -/
theorem sIdx_inj {Q t b Dw PTw PSw xw yw e t' b' Dw' PTw' PSw' xw' yw' e' : ℕ}
    (hb : b < 2) (hb' : b' < 2)
    (h1 : Dw < pwN Q) (h1' : Dw' < pwN Q) (h2 : PTw < pwN Q) (h2' : PTw' < pwN Q)
    (h3 : PSw < pwN Q) (h3' : PSw' < pwN Q) (h4 : xw < pwN Q) (h4' : xw' < pwN Q)
    (h5 : yw < pwN Q) (h5' : yw' < pwN Q) (he : e < boxN Q) (he' : e' < boxN Q)
    (h : sIdx Q t b Dw PTw PSw xw yw e = sIdx Q t' b' Dw' PTw' PSw' xw' yw' e') :
    t = t' ∧ b = b' ∧ Dw = Dw' ∧ PTw = PTw' ∧ PSw = PSw' ∧ xw = xw' ∧ yw = yw' ∧ e = e' := by
  unfold sIdx sBase at h
  obtain ⟨a1, r1⟩ := pk_inj he he' h
  obtain ⟨a2, r2⟩ := pk_inj h5 h5' a1
  obtain ⟨a3, r3⟩ := pk_inj h4 h4' a2
  obtain ⟨a4, r4⟩ := pk_inj h3 h3' a3
  obtain ⟨a5, r5⟩ := pk_inj h2 h2' a4
  obtain ⟨a6, r6⟩ := pk_inj h1 h1' a5
  obtain ⟨a7, r7⟩ := pk_inj hb hb' a6
  exact ⟨a7, r7, r6, r5, r4, r3, r2, r1⟩

/-- **The literal table exists.** -/
theorem exists_lits (m : ℕ) : ∃ lt : Lits, lt.Good m := by
  classical
  set Q := m ^ 4 with hQ
  set R := m ^ 3 with hR
  obtain ⟨D, A, hD1, hC⟩ := exists_common
    (fun p : Fin Q × Bool × Finset (Corner Q) × Finset (Corner Q) × Finset (Corner Q) × Finset (Corner Q) ×
        Finset (Corner Q) × Box Q =>
      MvPolynomial.coeff (expOf p.2.2.2.2.2.2.2)
        (sideS (kappa Q R) R p.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 (indV p.2.2.2.2.2.1) (indV p.2.2.2.2.2.2.1) p.2.1))
  have hbd : ∀ (t : Fin Q) (Dw : ℕ) (b : Bool) (PTw PSw xw yw : ℕ) (e : Box Q),
      IsScaled D A (MvPolynomial.coeff (expOf e) (sideT R t Dw b PTw PSw xw yw)) := by
    intro t Dw b PTw PSw xw yw e
    rw [sideT_eq_ind]
    exact hC (t, b, posSet Dw, posSet PTw, posSet PSw, posSet xw, posSet yw, e)
  let off : ℕ := ⌈A⌉₊
  have hoff : A ≤ off := Nat.le_ceil A
  let f : ℕ := Nat.clog 2 (2 * off + 1)
  have hf : 2 * off + 1 ≤ 2 ^ f := Nat.le_pow_clog (by norm_num) _
  let Dom := Fin Q × Bool × Fin (pwN Q) × Fin (pwN Q) × Fin (pwN Q) × Fin (pwN Q) × Fin (pwN Q) × Box Q
  let idx : Dom → ℕ := fun d => sIdx Q d.1 d.2.1.toNat d.2.2.1 d.2.2.2.1 d.2.2.2.2.1 d.2.2.2.2.2.1
    d.2.2.2.2.2.2.1 (wordIdx d.2.2.2.2.2.2.2)
  let val : Dom → ℕ := fun d => (coefZ D R d.1 d.2.2.1 d.2.1 d.2.2.2.1 d.2.2.2.2.1 d.2.2.2.2.2.1
    d.2.2.2.2.2.2.1 d.2.2.2.2.2.2.2 + off).toNat
  have hbool : ∀ b : Bool, b.toNat < 2 := fun b => by cases b <;> simp
  have hinj : Function.Injective idx := by
    rintro ⟨t1, b1, D1, p1, s1, x1, y1, e1⟩ ⟨t2, b2, D2, p2, s2, x2, y2, e2⟩ h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sIdx_inj (hbool b1) (hbool b2)
      D1.2 D2.2 p1.2 p2.2 s1.2 s2.2 x1.2 x2.2 y1.2 y2.2 (wordIdx_lt e1) (wordIdx_lt e2) h
    have e12 : e1 = e2 := by
      rw [← wordOf_wordIdx (Nat.succ_pos (2 ^ Q)) e1, ← wordOf_wordIdx (Nat.succ_pos (2 ^ Q)) e2, h8]
    have b12 : b1 = b2 := by
      cases b1 <;> cases b2 <;> simp_all
    have t12 : t1 = t2 := Fin.ext h1
    have D12 : D1 = D2 := Fin.ext h3
    have p12 : p1 = p2 := Fin.ext h4
    have s12 : s1 = s2 := Fin.ext h5
    have x12 : x1 = x2 := Fin.ext h6
    have y12 : y1 = y2 := Fin.ext h7
    rw [t12, b12, D12, p12, s12, x12, y12, e12]
  have hlt : ∀ d : Dom, idx d < sSize Q := by
    rintro ⟨t1, b1, D1, p1, s1, x1, y1, e1⟩
    exact sIdx_lt t1.2 (hbool b1) D1.2 p1.2 s1.2 x1.2 y1.2 (wordIdx_lt e1)
  obtain ⟨sT, hsT, hfl⟩ := exists_packed_inj f (sSize Q) idx hinj hlt val
  refine ⟨⟨D, off, f, sT⟩, hD1, ?_, ⟨A, hbd⟩, hsT⟩
  intro t b Dw PTw PSw xw yw h1 h2 h3 h4 h5 e
  have hs := scaled_small (D := D) (off := off) (f := f) (hbd t Dw b PTw PSw xw yw e) hoff hf
  have h6 := hfl (t, b, ⟨Dw, h1⟩, ⟨PTw, h2⟩, ⟨PSw, h3⟩, ⟨xw, h4⟩, ⟨yw, h5⟩, e) hs.2
  show ((fld f sT (sIdx Q t b.toNat Dw PTw PSw xw yw (wordIdx e)) : ℕ) : ℤ) - off = _
  have h7 : fld f sT (sIdx Q t b.toNat Dw PTw PSw xw yw (wordIdx e)) =
      (scaled D (MvPolynomial.coeff (expOf e) (sideT R t Dw b PTw PSw xw yw)) + off).toNat := h6
  rw [h7, hs.1, add_sub_cancel_right]
  rfl

/-- The constant of the word length. -/
def wConst (m : ℕ) (lt : Lits) : ℕ := 2 + (m ^ 4 + 3) + clOf m + Lits.wid m lt + 1

/-- **A sufficient word length.** Here `K = (6 * m ^ 4) ^ m ^ 4`. -/
theorem big_of_le {m h M v fw W : ℕ} {lt : Lits}
    (hW : wConst m lt * ((6 * m ^ 4) ^ m ^ 4 + h + 2 * M + v + fw + 3) ^ 3 ≤ W) :
    Big m h M v fw W lt := by
  set K := (6 * m ^ 4) ^ m ^ 4 with hK
  set X := K + h + 2 * M + v + fw + 3 with hX
  have hX1 : 1 ≤ X := by omega
  have hX3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
  have hXX : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) _
  have hXX2 : X * X ≤ X ^ 3 := by
    calc X * X = X * X * 1 := by ring
      _ ≤ X * X * X := Nat.mul_le_mul_left _ hX1
      _ = X ^ 3 := by ring
  have hA : K + h + 2 * M + v + 3 ≤ X := by omega
  have hlt : ∀ y k, y ≤ k * X ^ 3 → k < wConst m lt → y < W := by
    intro y k h1 h2
    have h3 : (k + 1) * X ^ 3 ≤ wConst m lt * X ^ 3 := Nat.mul_le_mul_right _ h2
    rw [add_mul, one_mul] at h3
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine hlt _ 1 ?_ (by unfold wConst; omega)
    rw [one_mul]
    exact Nat.pow_le_pow_left hA _
  · refine hlt _ (m ^ 4 + 3) ?_ (by unfold wConst; omega)
    calc (m ^ 4 + 3) * (K + h + 2 * M + v + 3) ≤ (m ^ 4 + 3) * X := Nat.mul_le_mul_left _ hA
      _ ≤ (m ^ 4 + 3) * X ^ 3 := Nat.mul_le_mul_left _ hXX
  · refine hlt _ (clOf m) ?_ (by unfold wConst; omega)
    exact Nat.mul_le_mul_left _ (hA.trans hXX)
  · refine hlt _ 1 ?_ (by unfold wConst; omega)
    rw [one_mul]
    calc (K + h + 2 * M + v + 3) * (fw + 1) ≤ X * X := Nat.mul_le_mul hA (by omega)
      _ ≤ X ^ 3 := hXX2
  · refine hlt _ (Lits.wid m lt) ?_ (by unfold wConst; omega)
    exact Nat.le_mul_of_pos_right _ hX3

end OnePigeonhole.Pseudo.Leaf
