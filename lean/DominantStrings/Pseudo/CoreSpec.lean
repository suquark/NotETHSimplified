import DominantStrings.Pseudo.StepSpec
import DominantStrings.Pseudo.BaseSpec

/-!
# The chain as a program

`wD`, `FD` are the weights and the word functions after `d` steps, for the code in the frame. `coreE` sums over the codes.
-/

namespace DominantStrings.Pseudo

open Finset TransposeBase.Pseudo TransposeBase.Pseudo.Leaf

/-- The weights after `d` steps. -/
def wD (L H sc c : ℕ) (w0 : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0 => w0
  | d + 1 => (stepLev (Kd L H (d + 1)) (baseD L H d) sc c (wD L H sc c w0 d)).newW

/-- The word functions after `d` steps. -/
noncomputable def FD (L H sc c : ℕ) (w0 : ℕ → ℕ → ℕ) (F0 : ℕ → (ℕ → ℕ) → ℤ) : ℕ → ℕ → (ℕ → ℕ) → ℤ
  | 0 => F0
  | d + 1 => (stepLev (Kd L H (d + 1)) (baseD L H d) sc c (wD L H sc c w0 d)).stepF (FD L H sc c w0 F0 d)

/-- The code of a chain is valid. -/
def validAll (L H c : ℕ) : Prop :=
  ∀ d < H, validCode (Kd L H (d + 1)) (c / 2 ^ baseD L H d % 2 ^ Kd L H (d + 1) ^ 4)

namespace CoreSpec

/-! ### The sizes of the levels -/

theorem Kd_zero (L H : ℕ) : Kd L H 0 = Ktow L H := rfl

theorem Kd_self (L H : ℕ) : Kd L H H = L := by
  simp [Kd, Ktow]

/-- A level has the square of the number of words of the next level. -/
theorem Kd_eq_mul {L H d : ℕ} (hd : d < H) : Kd L H d = Kd L H (d + 1) * Kd L H (d + 1) := by
  unfold Kd
  obtain ⟨h, rfl⟩ : ∃ h, H = d + 1 + h := ⟨H - (d + 1), by omega⟩
  have e1 : d + 1 + h - d = h + 1 := by omega
  have e2 : d + 1 + h - (d + 1) = h := by omega
  rw [e1, e2]
  rfl

theorem Ktow_mono {L : ℕ} {h h' : ℕ} (hh : h ≤ h') : Ktow L h ≤ Ktow L h' := by
  induction hh with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_mul_self _)

theorem le_Ktow (L h : ℕ) : L ≤ Ktow L h := Ktow_mono (Nat.zero_le h)

theorem le_Kd (L H d : ℕ) : L ≤ Kd L H d := le_Ktow L _

theorem Kd_le (L H d : ℕ) : Kd L H d ≤ Ktow L H := Ktow_mono (Nat.sub_le H d)

theorem Kd_pos {L : ℕ} (hL : 0 < L) (H d : ℕ) : 0 < Kd L H d := Ktow_pos hL _

theorem baseD_add_chainBits (L H d : ℕ) (hd : d ≤ H) : baseD L H d + chainBits L (H - d) = chainBits L H := by
  induction d with
  | zero => simp [baseD]
  | succ d ih =>
    have ih' := ih (by omega)
    have e : H - d = (H - (d + 1)) + 1 := by omega
    rw [e, chainBits] at ih'
    simp only [baseD, Kd]
    omega

theorem baseD_le (L H d : ℕ) (hd : d ≤ H) : baseD L H d ≤ chainBits L H := by
  have := baseD_add_chainBits L H d hd
  omega

theorem baseD_succ_le (L H d : ℕ) (hd : d < H) : baseD L H d + Kd L H (d + 1) ^ 4 ≤ chainBits L H :=
  baseD_le L H (d + 1) hd

/-! ### The value of a code -/

/-- The codes of the first `d` steps are valid. -/
def validUpTo (L H c d : ℕ) : Prop :=
  ∀ d' < d, validCode (Kd L H (d' + 1)) (c / 2 ^ baseD L H d' % 2 ^ Kd L H (d' + 1) ^ 4)

theorem validUpTo_zero (L H c : ℕ) : validUpTo L H c 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem validUpTo_succ (L H c d : ℕ) :
    validUpTo L H c (d + 1) ↔
      validUpTo L H c d ∧ validCode (Kd L H (d + 1)) (c / 2 ^ baseD L H d % 2 ^ Kd L H (d + 1) ^ 4) := by
  constructor
  · intro h
    exact ⟨fun d' hd' => h d' (by omega), h d (by omega)⟩
  · rintro ⟨h1, h2⟩ d' hd'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd' with h | rfl
    · exact h1 d' h
    · exact h2

open Classical in
/-- The value of a chain, after `d` steps. -/
theorem chainVal_eq_aux (L H sc c : ℕ) (w0 : ℕ → ℕ → ℕ) (F0 : ℕ → (ℕ → ℕ) → ℤ) (d : ℕ) (hd : d ≤ H) :
    chainVal L sc H w0 F0 c =
      (if validUpTo L H c d then 1 else 0) *
        chainVal L sc (H - d) (wD L H sc c w0 d) (FD L H sc c w0 F0 d) (c / 2 ^ baseD L H d) := by
  induction d with
  | zero =>
    simp [validUpTo_zero, baseD, wD, FD]
  | succ d ih =>
    rw [ih (by omega)]
    have e : H - d = (H - (d + 1)) + 1 := by omega
    have hdiv : c / 2 ^ baseD L H (d + 1) = c / 2 ^ baseD L H d / 2 ^ Kd L H (d + 1) ^ 4 := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      rfl
    have hval : ∀ (w : ℕ → ℕ → ℕ) (F : ℕ → (ℕ → ℕ) → ℤ) (c' : ℕ),
        chainVal L sc ((H - (d + 1)) + 1) w F c' =
          if validCode (Kd L H (d + 1)) (c' % 2 ^ Kd L H (d + 1) ^ 4) then
            chainVal L sc (H - (d + 1))
              (stepLev (Kd L H (d + 1)) 0 sc (c' % 2 ^ Kd L H (d + 1) ^ 4) w).newW
              ((stepLev (Kd L H (d + 1)) 0 sc (c' % 2 ^ Kd L H (d + 1) ^ 4) w).stepF F) (c' / 2 ^ Kd L H (d + 1) ^ 4)
          else 0 := by
      intro w F c'
      rw [chainVal]
      simp only [stepLev, pow_zero, Nat.div_one, Nat.mod_mod, levOf, Kd]
    rw [e, hval, hdiv]
    have hlev : stepLev (Kd L H (d + 1)) 0 sc (c / 2 ^ baseD L H d % 2 ^ Kd L H (d + 1) ^ 4)
        (wD L H sc c w0 d) = stepLev (Kd L H (d + 1)) (baseD L H d) sc c (wD L H sc c w0 d) := by
      simp only [stepLev, pow_zero, Nat.div_one, Nat.mod_mod]
    rw [hlev]
    by_cases h1 : validUpTo L H c d
    · by_cases h2 : validCode (Kd L H (d + 1)) (c / 2 ^ baseD L H d % 2 ^ Kd L H (d + 1) ^ 4)
      · have h3 : validUpTo L H c (d + 1) := (validUpTo_succ L H c d).mpr ⟨h1, h2⟩
        rw [if_pos h1, if_pos h2, if_pos h3]
        rfl
      · have h3 : ¬ validUpTo L H c (d + 1) := fun h => h2 ((validUpTo_succ L H c d).mp h).2
        rw [if_neg h2, if_neg h3]
        simp
    · have h3 : ¬ validUpTo L H c (d + 1) := fun h => h1 ((validUpTo_succ L H c d).mp h).1
      rw [if_neg h1, if_neg h3]
      simp

end CoreSpec

open Classical in
/-- The value of a chain, from the top. -/
theorem chainVal_eq (L H sc c : ℕ) (w0 : ℕ → ℕ → ℕ) (F0 : ℕ → (ℕ → ℕ) → ℤ) :
    chainVal L sc H w0 F0 c =
      (if validAll L H c then 1 else 0) * val L (wD L H sc c w0 H) (FD L H sc c w0 F0 H) := by
  rw [CoreSpec.chainVal_eq_aux L H sc c w0 F0 H le_rfl, Nat.sub_self, chainVal]
  rfl

/-- The bound on the number of ends on the words of one `u`, at the depth `d`. `P` bounds the potential of the first level. -/
def EbD (L H P d : ℕ) : ℕ := Nat.sqrt (91 ^ d * P / (100 ^ d * Kd L H (d + 1)))

/-- The bound on the number of ends of the last level. `P` bounds the potential of the first level. -/
def Ef (H P : ℕ) : ℕ := Nat.sqrt (91 ^ H * P / 100 ^ H)

variable {m v : ℕ}

namespace CoreSpec

/-! ### The weights of the levels -/

theorem wD_symm (L H sc c : ℕ) {w0 : ℕ → ℕ → ℕ} (h0 : ∀ x y, w0 x y = w0 y x) (d : ℕ) :
    ∀ x y, wD L H sc c w0 d x y = wD L H sc c w0 d y x := by
  induction d with
  | zero => exact h0
  | succ d ih => exact fun x y => newW_symm (stepLev _ _ _ _ _) ih x y

theorem wD_total {L H sc c : ℕ} {w0 : ℕ → ℕ → ℕ} (hL : 0 < L) (hs : ∀ x y, w0 x y = w0 y x)
    (h0 : ∑ x ∈ range (Ktow L H), ∑ y ∈ range (Ktow L H), w0 x y ≤ sc) (d : ℕ) (hd : d ≤ H) :
    ∑ x ∈ range (Kd L H d), ∑ y ∈ range (Kd L H d), wD L H sc c w0 d x y ≤ sc := by
  induction d with
  | zero => exact h0
  | succ d ih =>
    have ih' := ih (by omega)
    rw [Kd_eq_mul (by omega : d < H)] at ih'
    exact (newW_total_le (stepLev (Kd L H (d + 1)) (baseD L H d) sc c (wD L H sc c w0 d)) (Kd_pos hL _ _)
      (wD_symm L H sc c hs d)).trans ih'

/-- The potential after `d` steps. -/
def PotD (L H sc c : ℕ) (w0 : ℕ → ℕ → ℕ) (d : ℕ) : ℕ :=
  Kd L H d ^ 2 * psi (Kd L H d) (wD L H sc c w0 d)

theorem PotD_step {L H sc c : ℕ} {w0 : ℕ → ℕ → ℕ} (hs : ∀ x y, w0 x y = w0 y x) {d : ℕ} (hd : d < H) :
    100 * PotD L H sc c w0 (d + 1) ≤ 91 * PotD L H sc c w0 d := by
  unfold PotD
  have h := potential_min (Kd L H (d + 1)) (wD L H sc c w0 d) (wD_symm L H sc c hs d)
    (c / 2 ^ baseD L H d % 2 ^ Kd L H (d + 1) ^ 4) sc
  have e : wD L H sc c w0 (d + 1) =
      Lev.newW ⟨Kd L H (d + 1), wD L H sc c w0 d, c / 2 ^ baseD L H d % 2 ^ Kd L H (d + 1) ^ 4,
        dirOf (Kd L H (d + 1)) (wD L H sc c w0 d) sc (c / 2 ^ baseD L H d % 2 ^ Kd L H (d + 1) ^ 4), sc⟩ := rfl
  rw [← e] at h
  rw [Kd_eq_mul hd]
  generalize Kd L H (d + 1) = K' at h ⊢
  generalize psi K' (wD L H sc c w0 (d + 1)) = p at h ⊢
  generalize psi (K' * K') (wD L H sc c w0 d) = q at h ⊢
  calc 100 * (K' ^ 2 * p) = K' ^ 2 * (100 * p) := by ring
    _ ≤ K' ^ 2 * (91 * K' ^ 2 * q) := Nat.mul_le_mul_left _ h
    _ = 91 * ((K' * K') ^ 2 * q) := by ring

theorem PotD_pow {L H sc c : ℕ} {w0 : ℕ → ℕ → ℕ} (hs : ∀ x y, w0 x y = w0 y x) (d : ℕ) (hd : d ≤ H) :
    100 ^ d * PotD L H sc c w0 d ≤ 91 ^ d * PotD L H sc c w0 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have ih' := ih (by omega)
    have h := PotD_step (L := L) (H := H) (sc := sc) (c := c) hs (d := d) (by omega)
    calc 100 ^ (d + 1) * PotD L H sc c w0 (d + 1) = 100 ^ d * (100 * PotD L H sc c w0 (d + 1)) := by ring
      _ ≤ 100 ^ d * (91 * PotD L H sc c w0 d) := Nat.mul_le_mul_left _ h
      _ = 91 * (100 ^ d * PotD L H sc c w0 d) := by ring
      _ ≤ 91 * (91 ^ d * PotD L H sc c w0 0) := Nat.mul_le_mul_left _ ih'
      _ = 91 ^ (d + 1) * PotD L H sc c w0 0 := by ring

/-- The number of ends on the words of one `u`, at each depth. -/
theorem ends_le_EbD {L H sc c P : ℕ} {w0 : ℕ → ℕ → ℕ} (hL : 0 < L) (hs : ∀ x y, w0 x y = w0 y x)
    (hp : PotD L H sc c w0 0 ≤ P) {d u : ℕ} (hd : d < H) (hu : u < Kd L H (d + 1)) :
    ∑ v ∈ range (Kd L H (d + 1)), ∑ y ∈ range (Kd L H (d + 1) * Kd L H (d + 1)),
        wD L H sc c w0 d ((stepLev (Kd L H (d + 1)) (baseD L H d) sc c (wD L H sc c w0 d)).wd u v) y ≤ EbD L H P d := by
  have h1 := ends_row_sq_le (stepLev (Kd L H (d + 1)) (baseD L H d) sc c (wD L H sc c w0 d)) (u := u) hu
  change (∑ v ∈ range (Kd L H (d + 1)), ∑ y ∈ range (Kd L H (d + 1) * Kd L H (d + 1)),
      wD L H sc c w0 d ((stepLev (Kd L H (d + 1)) (baseD L H d) sc c (wD L H sc c w0 d)).wd u v) y) ^ 2 ≤
    Kd L H (d + 1) ^ 3 * psi (Kd L H (d + 1) * Kd L H (d + 1)) (wD L H sc c w0 d) at h1
  have h2 : 100 ^ d * PotD L H sc c w0 d ≤ 91 ^ d * P :=
    (PotD_pow (L := L) (H := H) (sc := sc) (c := c) hs d hd.le).trans (Nat.mul_le_mul_left _ hp)
  unfold PotD at h2
  rw [Kd_eq_mul hd] at h2
  have hK := Kd_pos hL H (d + 1)
  unfold EbD
  generalize (∑ v ∈ range (Kd L H (d + 1)), ∑ y ∈ range (Kd L H (d + 1) * Kd L H (d + 1)),
      wD L H sc c w0 d ((stepLev (Kd L H (d + 1)) (baseD L H d) sc c (wD L H sc c w0 d)).wd u v) y) = E at h1 ⊢
  generalize Kd L H (d + 1) = K' at h1 h2 hK ⊢
  generalize psi (K' * K') (wD L H sc c w0 d) = q at h1 h2
  rw [Nat.le_sqrt', Nat.le_div_iff_mul_le (by positivity)]
  calc E ^ 2 * (100 ^ d * K') = 100 ^ d * (E ^ 2 * K') := by ring
    _ ≤ 100 ^ d * ((K' ^ 3 * q) * K') := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
    _ = 100 ^ d * ((K' * K') ^ 2 * q) := by ring
    _ ≤ 91 ^ d * P := h2

/-- The number of ends of the last level. -/
theorem ends_le_Ef {L H sc c P : ℕ} {w0 : ℕ → ℕ → ℕ} (hs : ∀ x y, w0 x y = w0 y x)
    (hp : PotD L H sc c w0 0 ≤ P) :
    ∑ x ∈ range L, ∑ y ∈ range L, wD L H sc c w0 H x y ≤ Ef H P := by
  have h1 := ends_all_sq_le L (wD L H sc c w0 H)
  have h2 := PotD_pow (L := L) (H := H) (sc := sc) (c := c) hs H le_rfl
  unfold PotD at h2
  rw [Kd_self] at h2
  change _ ≤ 91 ^ H * PotD L H sc c w0 0 at h2
  unfold Ef
  rw [Nat.le_sqrt', Nat.le_div_iff_mul_le (by positivity)]
  calc _ ≤ (L ^ 2 * psi L (wD L H sc c w0 H)) * 100 ^ H := Nat.mul_le_mul_right _ h1
    _ = 100 ^ H * (L ^ 2 * psi L (wD L H sc c w0 H)) := by ring
    _ ≤ 91 ^ H * PotD L H sc c w0 0 := h2
    _ ≤ 91 ^ H * P := Nat.mul_le_mul_left _ hp

/-! ### The program of the last level -/

/-- The bound on the operations of `endsE` and `offE`. -/
def endsCost (K C : ℕ) : ℕ := 1 + 1 + K * (C + 1)

/-- The numbers of the word `v`, read from one number `Z`. -/
def readB (L : ℕ) (w : ℕ → ℕ → ℕ) (Z : ℕ) : ℕ → ℕ → ℕ :=
  fun v => viewL L (w v) (viewL L (fun v => ∑ y ∈ range L, w v y) Z v)

/-- The field of the numbers of the word in the variable `ix`, read from the number in the variable `iZ`. -/
def zxE (wt : ℕ → ℕ → ℕ → Expr) (L iZ ix ig : ℕ) : Expr :=
  .mod (.div (.var iZ) (.pow2 (.sum (.var ix) (endsE wt L (ig + 1) 0)))) (.pow2 (endsE wt L ig ix))

/-- The marks of one pair of words in `finalE`. -/
def testE (wt : ℕ → ℕ → ℕ → Expr) (L g : ℕ) : Expr :=
  .letE (zxE wt L 2 1 (g + 3)) <|
  .letE (zxE wt L 3 1 (g + 4)) <|
  .ite (.var 2) (.var 3) (.lit 1) <|
  .letE (.mod (.div (.var 1) (.pow2 (offE wt (g + 5) 3 2))) (.pow2 (wt (g + 5) 3 2))) <|
  .letE (.mod (.div (.var 1) (.pow2 (offE wt (g + 6) 3 4))) (.pow2 (wt (g + 6) 3 4))) <|
  .letE (wt (g + 7) 5 4) <|
    mkWE 0 2 1

theorem finalE_eq (L : ℕ) (wt word : ℕ → ℕ → ℕ → Expr) (g : ℕ) :
    finalE L wt word g =
      .sum (.pow2 (.sum (.lit L) (endsE wt L (g + 1) 0)))
        (.mul (.prod (.lit L) (.prod (.lit L) (testE wt L g)))
          (.prod (.lit L) (.letE (zxE wt L 1 0 (g + 2)) (word (g + 3) 1 0)))) := rfl

/-- The bound on the operations of `zxE`. -/
def zxCost (L C : ℕ) : ℕ :=
  1 + (1 + 1 + (1 + (1 + 1 + L * (endsCost L C + 1)))) + (1 + endsCost L C)

/-- The bound on the operations of a field of a number. -/
def fieldCost (L C : ℕ) : ℕ := 1 + (1 + 1 + (1 + endsCost L C)) + (1 + C)

/-- The bound on the operations of `testE`; `T` bounds the weights. -/
def testCost (L C T : ℕ) : ℕ :=
  1 + zxCost L C + (1 + zxCost L C + (10 + 2 * fieldCost L C + C + (2 + T * 14)))

/-- The bound on the operations of `finalE`. -/
def finalCost (L Cw Cword E T : ℕ) : ℕ :=
  1 + (1 + (1 + 1 + L * (endsCost L Cw + 1))) +
    2 ^ E * ((1 + (1 + 1 + L * ((1 + 1 + L * (testCost L Cw T + 1)) + 1)) +
      (1 + 1 + L * ((1 + zxCost L Cw + Cword) + 1))) + 1)

/-- The sizes of the last level. -/
structure FinalBig (W L T : ℕ) (w : ℕ → ℕ → ℕ) : Prop where
  htot : ∑ x ∈ range L, ∑ y ∈ range L, w x y ≤ T
  hT : T < W
  hL : L < W

namespace FinalBig

variable {W L T : ℕ} {w : ℕ → ℕ → ℕ}

theorem pow_big {n : ℕ} (hB : FinalBig W L T w) (h : n ≤ T) : n < 2 ^ W :=
  (h.trans_lt hB.hT).trans Nat.lt_two_pow_self

theorem lt_W {n : ℕ} (hB : FinalBig W L T w) (h : n ≤ T) : n < W := h.trans_lt hB.hT

theorem L_big (hB : FinalBig W L T w) : L < 2 ^ W := hB.hL.trans Nat.lt_two_pow_self

theorem ends_le (hB : FinalBig W L T w) {x : ℕ} (hx : x < L) : ∑ y ∈ range L, w x y ≤ T :=
  (single_le_sum (f := fun x => ∑ y ∈ range L, w x y) (fun _ _ => Nat.zero_le _) (mem_range.mpr hx)).trans hB.htot

theorem off_le (hB : FinalBig W L T w) {x y : ℕ} (hx : x < L) (hy : y ≤ L) : ∑ t ∈ range y, w x t ≤ T :=
  (sum_le_sum_of_subset (range_subset_range.mpr hy)).trans (hB.ends_le hx)

theorem rowOff_le (hB : FinalBig W L T w) {x : ℕ} (hx : x ≤ L) : ∑ t ∈ range x, ∑ y ∈ range L, w t y ≤ T :=
  (sum_le_sum_of_subset (range_subset_range.mpr hx)).trans hB.htot

theorem wt_le (hB : FinalBig W L T w) {x y : ℕ} (hx : x < L) (hy : y < L) : w x y ≤ T :=
  (le_total hx hy).trans hB.htot

end FinalBig

theorem viewL_lt {n : ℕ} {a : ℕ → ℕ} (Z : ℕ) {x : ℕ} (hx : x < n) : viewL n a Z x < 2 ^ a x := by
  rw [viewL, if_pos hx]
  exact Nat.mod_lt _ (by positivity)

section Final

variable {W L T C Cword : ℕ} {f : Frm} {wt word : ℕ → ℕ → ℕ → Expr} {w : ℕ → ℕ → ℕ} {F : ℕ → (ℕ → ℕ) → ℤ}

theorem run_endsE {K : ℕ} (hwt : WtSpec W f K wt w C) {g ix x : ℕ} {env : List ℕ} (hf : f.At env g)
    (hx : env.getD ix 0 = x) (hxK : x < K) (hKW : K < 2 ^ W) (hlt : ∑ y ∈ range K, w x y < 2 ^ W) :
    Run W (endsE wt K g ix) env (∑ y ∈ range K, w x y) (endsCost K C) :=
  Run.sum (Run.lit hKW) le_rfl
    (fun y hy => hwt (hf.up y) (by simpa using hx) (by simp) hxK hy) hlt

theorem run_offE {K : ℕ} (hwt : WtSpec W f K wt w C) {g ix iy x y : ℕ} {env : List ℕ} (hf : f.At env g)
    (hx : env.getD ix 0 = x) (hy : env.getD iy 0 = y) (hxK : x < K) (hyK : y ≤ K)
    (hlt : ∑ t ∈ range y, w x t < 2 ^ W) :
    Run W (offE wt g ix iy) env (∑ t ∈ range y, w x t) (endsCost K C) :=
  Run.sum (Run.var hy) hyK
    (fun t ht => hwt (hf.up t) (by simpa using hx) (by simp) hxK (by omega)) hlt

theorem run_zxE (hB : FinalBig W L T w) (hwt : WtSpec W f L wt w C) {iZ ix ig Z x : ℕ} {env : List ℕ}
    (hf : f.At env ig) (hZ : env.getD iZ 0 = Z) (hx : env.getD ix 0 = x) (hxL : x < L) :
    Run W (zxE wt L iZ ix ig) env (viewL L (fun v => ∑ y ∈ range L, w v y) Z x) (zxCost L C) := by
  have h1 : Run W (.sum (.var ix) (endsE wt L (ig + 1) 0)) env (∑ t ∈ range x, ∑ y ∈ range L, w t y)
      (1 + 1 + L * (endsCost L C + 1)) :=
    Run.sum (Run.var hx) hxL.le
      (fun t ht => run_endsE hwt (hf.up t) (by simp) (by omega) hB.L_big (hB.pow_big (hB.ends_le (by omega))))
      (hB.pow_big (hB.rowOff_le hxL.le))
  have h2 := run_endsE hwt hf hx hxL hB.L_big (hB.pow_big (hB.ends_le hxL))
  have h3 := Run.mod (Run.div (Run.var hZ) (Run.pow2 h1 (hB.lt_W (hB.rowOff_le hxL.le))))
    (Run.pow2 h2 (hB.lt_W (hB.ends_le hxL)))
  rw [viewL, if_pos hxL]
  exact h3

theorem run_field (hB : FinalBig W L T w) (hwt : WtSpec W f L wt w C) {g ia ib iz z a b : ℕ} {env : List ℕ}
    (hf : f.At env g) (hz : env.getD iz 0 = z) (ha : env.getD ia 0 = a) (hb : env.getD ib 0 = b)
    (haL : a < L) (hbL : b < L) :
    Run W (.mod (.div (.var iz) (.pow2 (offE wt g ia ib))) (.pow2 (wt g ia ib))) env (viewL L (w a) z b)
      (fieldCost L C) := by
  have h1 := run_offE hwt hf ha hb haL hbL.le (hB.pow_big (hB.off_le haL hbL.le))
  have h2 := hwt hf ha hb haL hbL
  have h3 := Run.mod (Run.div (Run.var hz) (Run.pow2 h1 (hB.lt_W (hB.off_le haL hbL.le))))
    (Run.pow2 h2 (hB.lt_W (hB.wt_le haL hbL)))
  rw [viewL, if_pos hbL]
  exact h3

theorem run_testE (hB : FinalBig W L T w) (hwt : WtSpec W f L wt w C) {g : ℕ} {env : List ℕ} (hf : f.At env g)
    {a b Z : ℕ} (ha : a < L) (hb : b < L) :
    RunZ W (testE wt L g) (b :: a :: Z :: env)
      (if a < b then mkW (w a b) (readB L w Z a b) (readB L w Z b a) else 1) (testCost L C T) := by
  have hf3 : f.At (b :: a :: Z :: env) (g + 3) := ((hf.up Z).up a).up b
  have h1 := run_zxE (C := C) hB hwt hf3 (iZ := 2) (ix := 1) (Z := Z) (x := a) (by simp) (by simp) ha
  generalize hZa : viewL L (fun v => ∑ y ∈ range L, w v y) Z a = Za at h1
  have h2 := run_zxE (C := C) hB hwt (hf3.up Za) (iZ := 3) (ix := 1) (Z := Z) (x := b) (by simp) (by simp) hb
  generalize hZb : viewL L (fun v => ∑ y ∈ range L, w v y) Z b = Zb at h2
  have hf5 := (hf3.up Za).up Zb
  have hAB : readB L w Z a b = viewL L (w a) Za b := by rw [← hZa]; rfl
  have hBA : readB L w Z b a = viewL L (w b) Zb a := by rw [← hZb]; rfl
  rw [hAB, hBA]
  have hW2 : 2 ≤ W := by have := hB.hL; have := hB.hT; omega
  have v2 : Run W (.var 2) (Zb :: Za :: b :: a :: Z :: env) b 1 := Run.var rfl
  have v3 : Run W (.var 3) (Zb :: Za :: b :: a :: Z :: env) a 1 := Run.var rfl
  have hneg : ¬ b ≤ a → RunZ W
      (.letE (.mod (.div (.var 1) (.pow2 (offE wt (g + 5) 3 2))) (.pow2 (wt (g + 5) 3 2))) <|
        .letE (.mod (.div (.var 1) (.pow2 (offE wt (g + 6) 3 4))) (.pow2 (wt (g + 6) 3 4))) <|
        .letE (wt (g + 7) 5 4) <| mkWE 0 2 1) (Zb :: Za :: b :: a :: Z :: env)
      (mkW (w a b) (viewL L (w a) Za b) (viewL L (w b) Zb a))
      (1 + fieldCost L C + (1 + fieldCost L C + (1 + C + (2 + T * 14)))) := by
    intro h
    have h3 := run_field (C := C) hB hwt hf5 (iz := 1) (ia := 3) (ib := 2) (z := Za) (a := a) (b := b)
      (by simp) (by simp) (by simp) ha hb
    have hf6 := hf5.up (viewL L (w a) Za b)
    have h4 := run_field (C := C) hB hwt hf6 (iz := 1) (ia := 3) (ib := 4) (z := Zb) (a := b) (b := a)
      (by simp) (by simp) (by simp) hb ha
    have hf7 := hf6.up (viewL L (w b) Zb a)
    have h5 := hwt hf7 (ix := 5) (iy := 4) (x := a) (y := b) (by simp) (by simp) ha hb
    have hmk := StepSpec.runZ_mkWE (W := W) (T := T)
      (env := w a b :: viewL L (w b) Zb a :: viewL L (w a) Za b :: Zb :: Za :: b :: a :: Z :: env)
      (iw := 0) (it := 2) (ih := 1) (d := w a b) (t := viewL L (w a) Za b) (h := viewL L (w b) Zb a)
      hW2 rfl rfl rfl (hB.lt_W (hB.wt_le ha hb)) (hB.wt_le ha hb)
    exact RunZ.letE h3 (RunZ.letE h4 (RunZ.letE h5 hmk))
  refine RunZ.mono (RunZ.letE h1 <| RunZ.letE h2 <| RunZ.ite v2 v3 (fun h => RunZ.lit1.eq ?_)
    (fun h => (hneg h).eq ?_)) ?_
  · rw [if_neg (by omega)]
  · rw [if_pos (by omega)]
  · unfold testCost
    omega

/-- **The value of the last level.** -/
theorem finalE_spec {E : ℕ} (hB : FinalBig W L T w) (hE : ∑ x ∈ range L, ∑ y ∈ range L, w x y ≤ E)
    (hwt : WtSpec W f L wt w C) (hword : WordSpec W f L word w F Cword) {g : ℕ} {env : List ℕ} (hf : f.At env g) :
    RunZ W (finalE L wt word g) env (val L w F) (finalCost L C Cword E T) := by
  rw [finalE_eq]
  have hsum : Run W (.sum (.lit L) (endsE wt L (g + 1) 0)) env (∑ x ∈ range L, ∑ y ∈ range L, w x y)
      (1 + 1 + L * (endsCost L C + 1)) :=
    Run.sum (Run.lit hB.L_big) le_rfl
      (fun x hx => run_endsE hwt (hf.up x) (by simp) hx hB.L_big (hB.pow_big (hB.ends_le hx)))
      (hB.pow_big hB.htot)
  have hpow := Run.pow2 hsum (hB.lt_W hB.htot)
  have hbody : ∀ Z < 2 ^ ∑ x ∈ range L, ∑ y ∈ range L, w x y,
      RunZ W (.mul (.prod (.lit L) (.prod (.lit L) (testE wt L g)))
          (.prod (.lit L) (.letE (zxE wt L 1 0 (g + 2)) (word (g + 3) 1 0)))) (Z :: env)
        (marks L w (readB L w Z) * ∏ x ∈ range L, F x (readB L w Z x))
        (1 + (1 + 1 + L * ((1 + 1 + L * (testCost L C T + 1)) + 1)) +
          (1 + 1 + L * ((1 + zxCost L C + Cword) + 1))) := by
    intro Z _
    refine RunZ.mul
      (RunZ.prod (Run.lit hB.L_big) le_rfl fun a ha =>
        RunZ.prod (Run.lit hB.L_big) le_rfl fun b hb => run_testE hB hwt hf ha hb)
      (RunZ.prod (Run.lit hB.L_big) le_rfl fun x hx => ?_)
    have hf2 : f.At (x :: Z :: env) (g + 2) := (hf.up Z).up x
    have h1 := run_zxE (C := C) hB hwt hf2 (iZ := 1) (ix := 0) (Z := Z) (x := x) (by simp) (by simp) hx
    exact RunZ.letE h1 (hword (hf2.up _) (by simp) (by simp) hx (viewL_lt Z hx))
  have hk : 2 ^ ∑ x ∈ range L, ∑ y ∈ range L, w x y ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hE
  refine (RunZ.sum hpow hk hbody).eq ?_
  have hG := sum_viewL_two L L w (fun B => marks L w B * ∏ x ∈ range L, F x (B x))
  unfold val
  rw [← hG]
  rfl

end Final

/-! ### The test of the codes -/

/-- The bound on the operations of `validStepE`. -/
def validStepCost (K' : ℕ) : ℕ :=
  1 + 1 + K' * ((1 + 1 + K' * ((1 + 1 + K' * ((1 + 1 + K' * (100 + 1)) + 1)) + 1)) + 1)

/-- The bound on the operations of `validD`. -/
def validCost (L H : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + validCost L H d + validStepCost (Kd L H (d + 1))

/-- The body of `validStepE`. -/
def validBodyE (K' base g : ℕ) : Expr :=
  .ite (.ite (.var 2) (.var 3) (.lit 0) (.ite (.var 0) (.var 1) (.lit 0) (.lit 1))) (.lit 0)
    (.ite (bitX (g + 4) (.add (.lit base)
      (.add (.mul (.add (.mul (.add (.mul (.var 3) (.lit K')) (.var 2)) (.lit K')) (.var 1)) (.lit K')) (.var 0))))
      (.lit 0) (.lit 1) (.lit 0))
    (.lit 1)

theorem validStepE_eq (K' base g : ℕ) :
    validStepE K' base g =
      .prod (.lit K') (.prod (.lit K') (.prod (.lit K') (.prod (.lit K') (validBodyE K' base g)))) := rfl

theorem digit_lt' {K n x b : ℕ} (hx : x < n) (hb : b < K) : x * K + b < n * K := by
  calc x * K + b < x * K + K := by omega
    _ = (x + 1) * K := by ring
    _ ≤ n * K := Nat.mul_le_mul_right _ hx

/-- The index of a bit of a code. -/
theorem idx_lt {K' a a' b b' : ℕ} (ha : a < K') (ha' : a' < K') (hb : b < K') (hb' : b' < K') :
    ((a * K' + a') * K' + b) * K' + b' < K' ^ 4 := by
  have h := digit_lt' (digit_lt' (digit_lt' ha ha') hb) hb'
  have e : K' * K' * K' * K' = K' ^ 4 := by ring
  rwa [e] at h

theorem run_validBody {W K' base g c a a' b b' : ℕ} {env : List ℕ} (hK : 0 < K') (hc : env.getD g 0 = c)
    (hW : K' ^ 4 + base < W) (hW2 : 2 ≤ W) (ha : a < K') (ha' : a' < K') (hb : b < K') (hb' : b' < K') :
    RunZ W (validBodyE K' base g) (b' :: b :: a' :: a :: env)
      (if ¬ (a < a' ∧ b < b') → c.testBit (base + (((a * K' + a') * K' + b) * K' + b')) = false then 1 else 0)
      100 := by
  have h3 := idx_lt ha ha' hb hb'
  have e1 : a * K' + a' ≤ (a * K' + a') * K' := Nat.le_mul_of_pos_right _ hK
  have e2 : (a * K' + a') * K' + b ≤ ((a * K' + a') * K' + b) * K' := Nat.le_mul_of_pos_right _ hK
  have e0 : K' ≤ K' ^ 4 := Nat.le_self_pow (by norm_num) K'
  have hbig : ∀ n, n < W → n < 2 ^ W := fun n hn => hn.trans Nat.lt_two_pow_self
  have hl0 : (0 : ℕ) < 2 ^ W := Nat.two_pow_pos W
  have hl1 : (1 : ℕ) < 2 ^ W := Nat.one_lt_two_pow (by omega)
  generalize henv : b' :: b :: a' :: a :: env = env'
  have r3 : Run W (.var 3) env' a 1 := Run.var (by rw [← henv]; rfl)
  have r2 : Run W (.var 2) env' a' 1 := Run.var (by rw [← henv]; rfl)
  have r1 : Run W (.var 1) env' b 1 := Run.var (by rw [← henv]; rfl)
  have r0 : Run W (.var 0) env' b' 1 := Run.var (by rw [← henv]; rfl)
  have rK : Run W (.lit K') env' K' 1 := Run.lit (hbig _ (by omega))
  have rb : Run W (.lit base) env' base 1 := Run.lit (hbig _ (by omega))
  have i1 := Run.add (Run.mul r3 rK (hbig _ (by omega))) r2 (hbig _ (by omega))
  have i2 := Run.add (Run.mul i1 rK (hbig _ (by omega))) r1 (hbig _ (by omega))
  have i3 := Run.add (Run.mul i2 rK (hbig _ (by omega))) r0 (hbig _ (by omega))
  have i4 := Run.add rb i3 (hbig _ (by omega))
  have hbit := Run.bitX (ki := g + 4) (x := c) (by rw [← henv]; simpa using hc) i4 (by omega) hW2
  have rl0 : Run W (.lit 0) env' 0 1 := Run.lit hl0
  have hcond : Run W (.ite (.var 2) (.var 3) (.lit 0) (.ite (.var 0) (.var 1) (.lit 0) (.lit 1))) env'
      (if a < a' ∧ b < b' then 1 else 0) (1 + 1 + 1 + (1 + (1 + 1 + 1 + (1 + 1)))) := by
    refine Run.ite r2 r3 (fun h => rl0.eq ?_) (fun h => Run.ite r0 r1 (fun h2 => rl0.eq ?_) (fun h2 => (Run.lit hl1).eq ?_))
    · rw [if_neg (by omega)]
    · rw [if_neg (by omega)]
    · rw [if_pos (by omega)]
  refine (RunZ.ite hcond rl0 (fun h => RunZ.ite hbit rl0 (fun hb0 => RunZ.lit1.eq ?_) (fun hb0 => RunZ.lit0.eq ?_))
    (fun h => RunZ.lit1.eq ?_)).mono ?_
  · refine (if_pos fun _ => ?_).symm
    cases hv : c.testBit (base + (((a * K' + a') * K' + b) * K' + b')) with
    | false => rfl
    | true => rw [hv] at hb0; simp at hb0
  · refine (if_neg fun hh => ?_).symm
    have hn : ¬ (a < a' ∧ b < b') := fun hr => by
      rw [if_pos hr] at h
      omega
    rw [hh hn] at hb0
    simp at hb0
  · refine (if_pos fun hn => ?_).symm
    refine absurd ?_ hn
    by_contra hr
    rw [if_neg hr] at h
    omega
  · simp only [Nat.reduceAdd, Nat.reduceLeDiff]

/-- The bits of the code of one step are bits of the code of the chain. -/
theorem validCode_iff (K' c base : ℕ) :
    validCode K' (c / 2 ^ base % 2 ^ K' ^ 4) ↔
      ∀ a < K', ∀ a' < K', ∀ b < K', ∀ b' < K', ¬ (a < a' ∧ b < b') →
        c.testBit (base + (((a * K' + a') * K' + b) * K' + b')) = false := by
  have hbit : ∀ a < K', ∀ a' < K', ∀ b < K', ∀ b' < K',
      (c / 2 ^ base % 2 ^ K' ^ 4).testBit (((a * K' + a') * K' + b) * K' + b') =
        c.testBit (base + (((a * K' + a') * K' + b) * K' + b')) := by
    intro a ha a' ha' b hb b' hb'
    rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true (idx_lt ha ha' hb hb'), Bool.true_and,
      Nat.add_comm]
  constructor
  · intro h a ha a' ha' b hb b' hb' hn
    rw [← hbit a ha a' ha' b hb b' hb']
    exact h a ha a' ha' b hb b' hb' hn
  · intro h a ha a' ha' b hb b' hb' hn
    rw [hbit a ha a' ha' b hb b' hb']
    exact h a ha a' ha' b hb b' hb' hn

/-- **The test of the code of one step.** -/
theorem validStep_spec {W K' base g c : ℕ} {env : List ℕ} (hK : 0 < K') (hc : env.getD g 0 = c)
    (hW : K' ^ 4 + base < W) (hW2 : 2 ≤ W) :
    RunZ W (validStepE K' base g) env (if validCode K' (c / 2 ^ base % 2 ^ K' ^ 4) then 1 else 0)
      (validStepCost K') := by
  have hKbig : K' < 2 ^ W := ((Nat.le_self_pow (by norm_num) K').trans_lt (by omega : K' ^ 4 < W)).trans
    Nat.lt_two_pow_self
  rw [validStepE_eq]
  refine (RunZ.prod (Run.lit hKbig) le_rfl fun a ha =>
    RunZ.prod (Run.lit hKbig) le_rfl fun a' ha' =>
    RunZ.prod (Run.lit hKbig) le_rfl fun b hb =>
    RunZ.prod (Run.lit hKbig) le_rfl fun b' hb' =>
    run_validBody hK hc hW hW2 ha ha' hb hb').eq ?_
  simp only [prod_test, mem_range]
  refine if_congr ?_ rfl rfl
  rw [validCode_iff]
  exact ⟨fun h a ha => h a (mem_range.mpr ha), fun h a ha => h a (mem_range.mp ha)⟩

open Classical in
/-- **The test of the codes of the first `d` steps.** -/
theorem validD_spec {W L H g c : ℕ} {env : List ℕ} (hL : 0 < L) (hc : env.getD g 0 = c) (hW : chainBits L H < W)
    (hW2 : 2 ≤ W) (d : ℕ) (hd : d ≤ H) :
    RunZ W (validD L H g d) env (if validUpTo L H c d then 1 else 0) (validCost L H d) := by
  induction d with
  | zero => exact RunZ.lit1.eq (if_pos (validUpTo_zero L H c)).symm
  | succ d ih =>
    have hb := baseD_succ_le L H d (by omega)
    refine (RunZ.mul (ih (by omega)) (validStep_spec (Kd_pos hL H (d + 1)) hc (by omega) hW2)).eq ?_
    by_cases h1 : validUpTo L H c d
    · by_cases h2 : validCode (Kd L H (d + 1)) (c / 2 ^ baseD L H d % 2 ^ Kd L H (d + 1) ^ 4)
      · rw [if_pos h1, if_pos h2, if_pos ((validUpTo_succ L H c d).mpr ⟨h1, h2⟩), one_mul]
      · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 ((validUpTo_succ L H c d).mp h).2), mul_zero]
    · rw [if_neg h1, if_neg (fun h => h1 ((validUpTo_succ L H c d).mp h).1), zero_mul]

end CoreSpec

/-- All the data of the core program. `f` is the frame; its code does not matter. `P` bounds the potential of the first level. -/
structure CoreOK (W : ℕ) (f : Frm) (L H : ℕ) (N : BaseNet m v) (nodeG : ℕ → Expr) (Unode P : ℕ) : Prop where
  hL : 2 ≤ L
  base : ∀ c, BaseOK W { f with c := c } N (Ktow L H) nodeG Unode
  rect : RectBig W f.sc f.bk
  hbits : (Ktow L H + 1) ^ 4 + chainBits L H + 8 * f.sc + 8 < W
  hpsi : Ktow L H ^ 2 * psi (Ktow L H) N.w0 ≤ P

namespace CoreSpec

/-! ### The specifications at each depth -/

/-- The bound on the operations of the weights at depth `d`. -/
def CwD (L H m : ℕ) : ℕ → ℕ
  | 0 => wt0Cost m
  | d + 1 => nextWtCost (Kd L H (d + 1)) (CwD L H m d)

/-- The bound on the operations of the word functions at depth `d`. -/
def CwordD (L H m v Unode P : ℕ) : ℕ → ℕ
  | 0 => word0Cost (Ktow L H) m v Unode
  | d + 1 => nextWordCost (Kd L H (d + 1)) (CwD L H m d) (CwordD L H m v Unode P d) (EbD L H P d) (2 * m)

/-- The data of the core program, for a frame with a code. -/
structure FrameOK (W : ℕ) (fc : Frm) (L H : ℕ) (N : BaseNet m v) (nodeG : ℕ → Expr) (Unode P : ℕ) : Prop where
  hL : 2 ≤ L
  base : BaseOK W fc N (Ktow L H) nodeG Unode
  rect : RectBig W fc.sc fc.bk
  hbits : (Ktow L H + 1) ^ 4 + chainBits L H + 8 * fc.sc + 8 < W
  hpsi : Ktow L H ^ 2 * psi (Ktow L H) N.w0 ≤ P

theorem frameOK {W L H Unode P : ℕ} {f : Frm} {N : BaseNet m v} {nodeG : ℕ → Expr}
    (h : CoreOK W f L H N nodeG Unode P) (c : ℕ) : FrameOK W { f with c := c } L H N nodeG Unode P :=
  ⟨h.hL, h.base c, h.rect, h.hbits, h.hpsi⟩

/-- **The programs at each depth.** -/
theorem specs_D {W L H Unode P : ℕ} {fc : Frm} {N : BaseNet m v} {nodeG : ℕ → Expr}
    (h : FrameOK W fc L H N nodeG Unode P) (d : ℕ) (hd : d ≤ H) :
    WtSpec W fc (Kd L H d) (wtD L H d) (wD L H (2 * m) fc.c N.w0 d) (CwD L H m d) ∧
      WordSpec W fc (Kd L H d) (wordD L H nodeG d) (wD L H (2 * m) fc.c N.w0 d)
        (FD L H (2 * m) fc.c N.w0 (flipF (Ktow L H) N.w0 N.F0) d) (CwordD L H m v Unode P d) := by
  have hL : 0 < L := by have := h.hL; omega
  have hsc : fc.sc = 2 * m := h.base.hsc
  have hs := N.w0_symm
  have htot0 := N.w0_total h.base.hr
  have hp : PotD L H (2 * m) fc.c N.w0 0 ≤ P := h.hpsi
  induction d with
  | zero => exact ⟨wt0_spec h.base, word0_spec h.base⟩
  | succ d ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hd' : d < H := by omega
    have htotd := wD_total (c := fc.c) hL hs htot0 d hd'.le
    rw [Kd_eq_mul hd'] at ih1 ih2 htotd
    have hK := Kd_pos hL H (d + 1)
    have hB : StepBig W fc (Kd L H (d + 1)) (baseD L H d) (wD L H (2 * m) fc.c N.w0 d) := by
      refine ⟨h.rect, ?_, wD_symm L H (2 * m) fc.c hs d, by rw [hsc]; exact htotd⟩
      have h1 := Nat.pow_le_pow_left (Nat.succ_le_succ (Kd_le L H (d + 1))) 4
      have h2 := baseD_le L H d hd'.le
      have h3 := h.hbits
      simp only [Nat.succ_eq_add_one] at h1
      omega
    have hE : ∀ u < Kd L H (d + 1), ∑ v ∈ range (Kd L H (d + 1)), ∑ y ∈ range (Kd L H (d + 1) * Kd L H (d + 1)),
        wD L H (2 * m) fc.c N.w0 d ((stepLev (Kd L H (d + 1)) (baseD L H d) fc.sc fc.c
          (wD L H (2 * m) fc.c N.w0 d)).wd u v) y ≤ EbD L H P d := by
      intro u hu
      rw [hsc]
      exact ends_le_EbD hL hs hp hd' hu
    have h1 : WtSpec W fc (Kd L H (d + 1)) (wtNext (Kd L H (d + 1)) (baseD L H d) (wtD L H d))
        (stepLev (Kd L H (d + 1)) (baseD L H d) fc.sc fc.c (wD L H (2 * m) fc.c N.w0 d)).newW
        (nextWtCost (Kd L H (d + 1)) (CwD L H m d)) := wtNext_spec hB hK ih1
    have h2 : WordSpec W fc (Kd L H (d + 1))
        (wordNext (Kd L H (d + 1)) (baseD L H d) (wtD L H d) (wordD L H nodeG d))
        (stepLev (Kd L H (d + 1)) (baseD L H d) fc.sc fc.c (wD L H (2 * m) fc.c N.w0 d)).newW
        ((stepLev (Kd L H (d + 1)) (baseD L H d) fc.sc fc.c (wD L H (2 * m) fc.c N.w0 d)).stepF
          (FD L H (2 * m) fc.c N.w0 (flipF (Ktow L H) N.w0 N.F0) d))
        (nextWordCost (Kd L H (d + 1)) (CwD L H m d) (CwordD L H m v Unode P d) (EbD L H P d) fc.sc) :=
      wordNext_spec hB hK ih1 ih2 hE
    rw [hsc] at h1 h2
    exact ⟨h1, h2⟩

/-- The bound on the operations of the body of the sum over the codes. -/
def bodyCost (L H m v Unode P : ℕ) : ℕ :=
  1 + validCost L H H + finalCost L (CwD L H m H) (CwordD L H m v Unode P H) (Ef H P) (2 * m)

/-- **The body of the sum over the codes.** -/
theorem core_body {W L H Unode P : ℕ} {fc : Frm} {N : BaseNet m v} {nodeG : ℕ → Expr}
    (h : FrameOK W fc L H N nodeG Unode P) :
    RunZ W (.mul (validD L H 0 H) (finalE L (wtD L H H) (wordD L H nodeG H) 0)) fc.list
      (chainVal L (2 * m) H N.w0 (flipF (Ktow L H) N.w0 N.F0) fc.c) (bodyCost L H m v Unode P) := by
  classical
  have hL : 0 < L := by have := h.hL; omega
  have hsc : fc.sc = 2 * m := h.base.hsc
  have hs := N.w0_symm
  have htot0 := N.w0_total h.base.hr
  have hp : PotD L H (2 * m) fc.c N.w0 0 ≤ P := h.hpsi
  have hf : fc.At fc.list 0 := ⟨[], rfl, rfl⟩
  obtain ⟨h1, h2⟩ := specs_D h H le_rfl
  have htot := wD_total (c := fc.c) hL hs htot0 H le_rfl
  rw [Kd_self] at h1 h2 htot
  have hbits := h.hbits
  have hLle : L ≤ (Ktow L H + 1) ^ 4 :=
    (le_Ktow L H).trans ((Nat.le_succ _).trans (Nat.le_self_pow (by norm_num) _))
  have hB : FinalBig W L (2 * m) (wD L H (2 * m) fc.c N.w0 H) :=
    ⟨htot, by rw [hsc] at hbits; omega, by omega⟩
  have hfin := finalE_spec hB (ends_le_Ef hs hp) h1 h2 hf
  have hval := validD_spec (W := W) (L := L) (H := H) (g := 0) (c := fc.c) (env := fc.list) hL rfl (by omega)
    (by
      have h2L := h.hL
      have : 2 ≤ (Ktow L H + 1) ^ 4 := by omega
      omega) H le_rfl
  refine (RunZ.mul hval hfin).eq ?_
  rw [chainVal_eq]
  rfl

/-! ### The cost

The named bounds of the other files are unfolded only in the six lemmas `wt0Cost_le`, `nextWtCost_le`, `rectCost_le`,
`word0Cost_le`, `nextWordCost_le`, `rectPart_le`. Their constants are values of the same bounds, so these lemmas do not depend on
the numbers in the definitions. -/

theorem rectCost_aux (A m v : ℕ) : A * (2 * m + 1) ^ 2 ≤ 8 * (A * (0 + 1) ^ 2) * (m + v + 1) ^ 3 := by
  have h1 : 2 * m + 1 ≤ 2 * (m + v + 1) := by omega
  have h2 : (2 * m + 1) ^ 2 ≤ (2 * (m + v + 1)) ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : (m + v + 1) ^ 2 ≤ (m + v + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : (2 * m + 1) ^ 2 ≤ 8 * (m + v + 1) ^ 3 := by
    calc (2 * m + 1) ^ 2 ≤ 4 * (m + v + 1) ^ 2 := by rw [mul_pow] at h2; exact h2
      _ ≤ 4 * (m + v + 1) ^ 3 := Nat.mul_le_mul_left _ h3
      _ ≤ 8 * (m + v + 1) ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
  calc A * (2 * m + 1) ^ 2 ≤ A * (8 * (m + v + 1) ^ 3) := Nat.mul_le_mul_left _ h4
    _ = 8 * (A * (0 + 1) ^ 2) * (m + v + 1) ^ 3 := by ring

theorem word0Cost_aux (A B K m v U : ℕ) (hB : 1 ≤ B) :
    A * (K + 1) * (m + 1) ^ 2 + (v + 1) * (U + B) ≤
      (A * (K + 1) * (0 + 1) ^ 2 + (0 + 1) * (0 + B)) * ((m + v + 1) ^ 3 * (U + 1)) := by
  have h1 : (m + 1) ^ 2 ≤ (m + v + 1) ^ 3 := by
    calc (m + 1) ^ 2 ≤ (m + v + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ ≤ (m + v + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : v + 1 ≤ (m + v + 1) ^ 3 :=
    (by omega : v + 1 ≤ m + v + 1).trans (Nat.le_self_pow (by norm_num) _)
  have h3 : U + B ≤ B * (U + 1) := by nlinarith
  have h4 : (m + v + 1) ^ 3 ≤ (m + v + 1) ^ 3 * (U + 1) := Nat.le_mul_of_pos_right _ (by omega)
  calc A * (K + 1) * (m + 1) ^ 2 + (v + 1) * (U + B)
      ≤ A * (K + 1) * ((m + v + 1) ^ 3 * (U + 1)) + (m + v + 1) ^ 3 * (B * (U + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (h1.trans h4)) (Nat.mul_le_mul h2 h3)
    _ = (A * (K + 1) * (0 + 1) ^ 2 + (0 + 1) * (0 + B)) * ((m + v + 1) ^ 3 * (U + 1)) := by ring

theorem mul3_le (a b c r x y y' z : ℕ) (hr : 1 ≤ r) (hy : y ≤ y') :
    a * x + b * y + c * z ≤ (a * (0 + 1) + b * r + c * (0 + 1)) * (x + y' + z) := by
  have hb : b ≤ b * r := Nat.le_mul_of_pos_right _ hr
  have ha : a ≤ a * (0 + 1) + b * r + c * (0 + 1) := by omega
  have hb' : b ≤ a * (0 + 1) + b * r + c * (0 + 1) := by omega
  have hc : c ≤ a * (0 + 1) + b * r + c * (0 + 1) := by omega
  rw [Nat.mul_add, Nat.mul_add]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ ha) (Nat.mul_le_mul hb' hy))
    (Nat.mul_le_mul_right _ hc)

theorem part_aux (a b R R0 T : ℕ) (hT : 1 ≤ T) (hR : R ≤ 8 * R0 * T) :
    a + (R + b) + 1 ≤ 8 * (a + (R0 + b) + 1) * T := by
  have h : a + b + 1 ≤ 8 * (a + b + 1) * T := by
    calc a + b + 1 ≤ 8 * (a + b + 1) := by omega
      _ ≤ 8 * (a + b + 1) * T := Nat.le_mul_of_pos_right _ hT
  calc a + (R + b) + 1 = R + (a + b + 1) := by ring
    _ ≤ 8 * R0 * T + 8 * (a + b + 1) * T := Nat.add_le_add hR h
    _ = 8 * (a + (R0 + b) + 1) * T := by ring

theorem wt0Cost_le (m : ℕ) : wt0Cost m ≤ wt0Cost 0 * (m + 1) := by
  unfold wt0Cost
  simp

theorem nextWtCost_le (K' C : ℕ) : nextWtCost K' C ≤ nextWtCost K' 0 * (C + 1) := by
  unfold nextWtCost
  simp

theorem rectCost_le (m v : ℕ) : rectCost (2 * m) ≤ 8 * rectCost 0 * (m + v + 1) ^ 3 := by
  unfold rectCost
  exact rectCost_aux _ m v

theorem word0Cost_le (K m v U : ℕ) : word0Cost K m v U ≤ word0Cost K 0 0 0 * ((m + v + 1) ^ 3 * (U + 1)) := by
  unfold word0Cost
  exact word0Cost_aux (5000 * (K + 1)) 100 K m v U (by norm_num)

/-- The part of the bound on `wordNext` for the factors of a rectangle. -/
def rectPart (sc : ℕ) : ℕ := nextWordCost 0 0 0 0 sc

theorem nextWordCost_le (K' Cw Cword Eb sc : ℕ) :
    nextWordCost K' Cw Cword Eb sc ≤
      2 ^ Eb * (nextWordCost K' 0 0 0 0 * ((Cw + 1) + rectPart sc + (Cword + 1))) := by
  unfold rectPart nextWordCost
  simp only [pow_zero, one_mul]
  refine Nat.mul_le_mul_left _ (mul3_le _ _ _ _ _ _ _ _ (by omega) ?_)
  simp only [zero_add, one_pow, mul_one, one_mul]
  omega

theorem rectPart_le (m v : ℕ) : rectPart (2 * m) ≤ 8 * rectPart 0 * (m + v + 1) ^ 3 := by
  have h := rectCost_le m v
  have hT : 1 ≤ (m + v + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  unfold rectPart nextWordCost
  simp only [pow_zero, zero_add, one_pow, mul_one, one_mul]
  generalize (m + v + 1) ^ 3 = X at *
  generalize rectCost (2 * m) = R at *
  generalize rectCost 0 = R0 at *
  nlinarith

/-- The constant of the weights at depth `d`. -/
def aD (L H : ℕ) : ℕ → ℕ
  | 0 => wt0Cost 0
  | d + 1 => nextWtCost (Kd L H (d + 1)) 0 * (aD L H d + 1)

/-- The constant of the factors of a rectangle. -/
def rectCoef : ℕ := 8 * rectPart 0

/-- The constant of the word functions at depth `d`. -/
def bD (L H : ℕ) : ℕ → ℕ
  | 0 => word0Cost (Ktow L H) 0 0 0
  | d + 1 => nextWordCost (Kd L H (d + 1)) 0 0 0 0 * ((aD L H d + 1) + rectCoef + (bD L H d + 1))

theorem one_le_S (m v U : ℕ) : 1 ≤ (m + v + 1) ^ 3 * (U + 1) :=
  Nat.mul_pos (by positivity) (by omega)

theorem m_le_S (m v U : ℕ) : m + 1 ≤ (m + v + 1) ^ 3 * (U + 1) := by
  calc m + 1 ≤ m + v + 1 := by omega
    _ ≤ (m + v + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    _ ≤ (m + v + 1) ^ 3 * (U + 1) := Nat.le_mul_of_pos_right _ (by omega)

theorem CwD_le (L H m d : ℕ) : CwD L H m d ≤ aD L H d * (m + 1) := by
  induction d with
  | zero => exact wt0Cost_le m
  | succ d ih =>
    calc CwD L H m (d + 1) = nextWtCost (Kd L H (d + 1)) (CwD L H m d) := rfl
      _ ≤ nextWtCost (Kd L H (d + 1)) 0 * (CwD L H m d + 1) := nextWtCost_le _ _
      _ ≤ nextWtCost (Kd L H (d + 1)) 0 * ((aD L H d + 1) * (m + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          rw [add_mul, one_mul]
          omega
      _ = aD L H (d + 1) * (m + 1) := by simp only [aD]; ring

theorem CwordD_le (L H m v U P d : ℕ) :
    CwordD L H m v U P d ≤ 2 ^ (∑ i ∈ range d, EbD L H P i) * (bD L H d * ((m + v + 1) ^ 3 * (U + 1))) := by
  induction d with
  | zero =>
    rw [sum_range_zero, pow_zero, one_mul]
    exact word0Cost_le _ m v U
  | succ d ih =>
    have hS1 := one_le_S m v U
    have hmS := m_le_S m v U
    have hR := rectPart_le m v
    have hCw := CwD_le L H m d
    have hle : (m + v + 1) ^ 3 ≤ (m + v + 1) ^ 3 * (U + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hN := nextWordCost_le (Kd L H (d + 1)) (CwD L H m d) (CwordD L H m v U P d) (EbD L H P d) (2 * m)
    have hP : 1 ≤ 2 ^ (∑ i ∈ range d, EbD L H P i) := Nat.one_le_two_pow
    have hb : CwordD L H m v U P (d + 1) =
        nextWordCost (Kd L H (d + 1)) (CwD L H m d) (CwordD L H m v U P d) (EbD L H P d) (2 * m) :=
      rfl
    have hbD : bD L H (d + 1) = nextWordCost (Kd L H (d + 1)) 0 0 0 0 * ((aD L H d + 1) + rectCoef + (bD L H d + 1)) := rfl
    rw [hb, hbD, sum_range_succ, pow_add]
    refine hN.trans ?_
    generalize (m + v + 1) ^ 3 * (U + 1) = S at *
    generalize (m + v + 1) ^ 3 = t at *
    generalize 2 ^ (∑ i ∈ range d, EbD L H P i) = T at *
    generalize 2 ^ EbD L H P d = Q at *
    generalize nextWordCost (Kd L H (d + 1)) 0 0 0 0 = N at *
    generalize CwD L H m d = Cw at *
    generalize CwordD L H m v U P d = Cword at *
    generalize aD L H d = a at *
    generalize bD L H d = b at *
    have h1 : Cw + 1 ≤ T * ((a + 1) * S) := by
      have h : Cw ≤ a * S := hCw.trans (Nat.mul_le_mul_left _ hmS)
      have h' : Cw + 1 ≤ (a + 1) * S := by rw [add_mul, one_mul]; omega
      exact h'.trans (Nat.le_mul_of_pos_left _ hP)
    have h2 : rectPart (2 * m) ≤ T * (rectCoef * S) :=
      (hR.trans (Nat.mul_le_mul_left _ hle)).trans (Nat.le_mul_of_pos_left _ hP)
    have h3 : Cword + 1 ≤ T * ((b + 1) * S) := by
      have hPS : 1 ≤ T * S := Nat.mul_pos hP hS1
      calc Cword + 1 ≤ T * (b * S) + T * S := Nat.add_le_add ih hPS
        _ = T * ((b + 1) * S) := by ring
    calc Q * (N * (Cw + 1 + rectPart (2 * m) + (Cword + 1)))
        ≤ Q * (N * (T * ((a + 1) * S) + T * (rectCoef * S) + T * ((b + 1) * S))) := by
          refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
          exact Nat.add_le_add (Nat.add_le_add h1 h2) h3
      _ = T * Q * (N * (a + 1 + rectCoef + (b + 1)) * S) := by ring

theorem finalCost_le (L Cw Cword E T : ℕ) :
    finalCost L Cw Cword E T ≤ 2 ^ E * (200 * (L + 1) ^ 4 * (Cw + Cword + T + 1)) := by
  have hP : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  unfold finalCost
  generalize 2 ^ E = P at *
  have hAB : (1 + (1 + (1 + 1 + L * (endsCost L Cw + 1)))) +
      ((1 + (1 + 1 + L * ((1 + 1 + L * (testCost L Cw T + 1)) + 1)) +
        (1 + 1 + L * ((1 + zxCost L Cw + Cword) + 1))) + 1) ≤ 200 * (L + 1) ^ 4 * (Cw + Cword + T + 1) := by
    unfold testCost zxCost fieldCost endsCost
    ring_nf
    omega
  calc _ ≤ P * (1 + (1 + (1 + 1 + L * (endsCost L Cw + 1)))) +
        P * ((1 + (1 + 1 + L * ((1 + 1 + L * (testCost L Cw T + 1)) + 1)) +
          (1 + 1 + L * ((1 + zxCost L Cw + Cword) + 1))) + 1) :=
        Nat.add_le_add_right (Nat.le_mul_of_pos_left _ hP) _
    _ = P * ((1 + (1 + (1 + 1 + L * (endsCost L Cw + 1)))) +
        ((1 + (1 + 1 + L * ((1 + 1 + L * (testCost L Cw T + 1)) + 1)) +
          (1 + 1 + L * ((1 + zxCost L Cw + Cword) + 1))) + 1)) := (Nat.mul_add _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hAB

/-- The constant of the core program. -/
def coreConst (L H : ℕ) : ℕ :=
  2 ^ chainBits L H * (validCost L H H + 5 + 200 * (L + 1) ^ 4 * (aD L H H + bD L H H + 3))

theorem coreCost_le (L H m v Unode P : ℕ) :
    1 + (1 + 1) + 2 ^ chainBits L H * (bodyCost L H m v Unode P + 1) ≤
      coreConst L H * (m + v + 1) ^ 3 * (Unode + 1) * 2 ^ ((∑ d ∈ range H, EbD L H P d) + Ef H P) := by
  have hfin := finalCost_le L (CwD L H m H) (CwordD L H m v Unode P H) (Ef H P) (2 * m)
  have hCw := CwD_le L H m H
  have hCword := CwordD_le L H m v Unode P H
  have hS1 := one_le_S m v Unode
  have hmS := m_le_S m v Unode
  have hT : 1 ≤ 2 ^ chainBits L H := Nat.one_le_two_pow
  have hP : 1 ≤ 2 ^ (∑ d ∈ range H, EbD L H P d) := Nat.one_le_two_pow
  have hQ : 1 ≤ 2 ^ Ef H P := Nat.one_le_two_pow
  have he : ∀ C t u X : ℕ, C * t * u * X = C * (t * u) * X := fun C t u X => by ring
  unfold bodyCost coreConst
  rw [pow_add, he]
  generalize (m + v + 1) ^ 3 * (Unode + 1) = S at *
  generalize 2 ^ chainBits L H = T at *
  generalize 2 ^ (∑ d ∈ range H, EbD L H P d) = X at *
  generalize 2 ^ Ef H P = Q at *
  generalize finalCost L (CwD L H m H) (CwordD L H m v Unode P H) (Ef H P) (2 * m) = F at *
  generalize CwD L H m H = Cw at *
  generalize CwordD L H m v Unode P H = Cword at *
  generalize aD L H H = a at *
  generalize bD L H H = b at *
  generalize 200 * (L + 1) ^ 4 = D at *
  generalize validCost L H H = V at *
  have h1 : Cw ≤ X * (a * S) :=
    (hCw.trans (Nat.mul_le_mul_left _ hmS)).trans (Nat.le_mul_of_pos_left _ hP)
  have hPS : 1 ≤ X * S := Nat.mul_pos hP hS1
  have hmX : 2 * m ≤ 2 * (X * S) := by
    have : S ≤ X * S := Nat.le_mul_of_pos_left _ hP
    omega
  have h2 : Cw + Cword + 2 * m + 1 ≤ X * (S * (a + b + 3)) := by
    calc Cw + Cword + 2 * m + 1 ≤ X * (a * S) + X * (b * S) + 2 * (X * S) + X * S :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 hCword) hmX) hPS
      _ = X * (S * (a + b + 3)) := by ring
  have h3 : F ≤ (D * (a + b + 3)) * (X * Q * S) := by
    calc F ≤ Q * (D * (Cw + Cword + 2 * m + 1)) := hfin
      _ ≤ Q * (D * (X * (S * (a + b + 3)))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = (D * (a + b + 3)) * (X * Q * S) := by ring
  have hZ : 1 ≤ X * Q * S := Nat.mul_pos (Nat.mul_pos hP hQ) hS1
  have h4 : V + 5 ≤ (V + 5) * (X * Q * S) := Nat.le_mul_of_pos_right _ hZ
  calc 1 + (1 + 1) + T * (1 + V + F + 1)
      ≤ T * 3 + T * (1 + V + F + 1) := Nat.add_le_add_right (by omega) _
    _ = T * (V + 5 + F) := by ring
    _ ≤ T * ((V + 5) * (X * Q * S) + (D * (a + b + 3)) * (X * Q * S)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add h4 h3)
    _ = T * (V + 5 + D * (a + b + 3)) * S * (X * Q) := by ring

end CoreSpec

/-- **The core program.** The value is the sum of the network, up to a fixed power of two. The constant `A` depends only on `L`, `H`,
and `P` is any bound on the potential of the first level. The environment is the frame without the code: the program binds the
code. -/
theorem core_spec (L H : ℕ) :
    ∃ A : ℕ, ∀ {W m v Unode P : ℕ} {f : Frm} {N : BaseNet m v} {nodeG : ℕ → Expr},
      CoreOK W f L H N nodeG Unode P →
      RunZ W (coreE L H nodeG) f.list.tail
        (2 ^ scaleTot L (2 * m) H * ∑ z : Fin m → Bool, ∏ α, N.φ α (fun e => z e.1))
        (A * (m + v + 1) ^ 3 * (Unode + 1) * 2 ^ ((∑ d ∈ range H, EbD L H P d) + Ef H P)) := by
  refine ⟨CoreSpec.coreConst L H, ?_⟩
  intro W m v Unode P f N nodeG h
  have hL : 0 < L := by have := h.hL; omega
  have hr := (h.base 0).hr
  have hbits := h.hbits
  have hpow : Run W (.pow2 (.lit (chainBits L H))) f.list.tail (2 ^ chainBits L H) (1 + 1) :=
    Run.pow2 (Run.lit (lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := W)))) (by omega)
  have hbody : ∀ c < 2 ^ chainBits L H,
      RunZ W (.mul (validD L H 0 H) (finalE L (wtD L H H) (wordD L H nodeG H) 0)) (c :: f.list.tail)
        (chainVal L (2 * m) H N.w0 (flipF (Ktow L H) N.w0 N.F0) c) (CoreSpec.bodyCost L H m v Unode P) :=
    fun c _ => CoreSpec.core_body (CoreSpec.frameOK h c)
  refine ((RunZ.sum hpow le_rfl hbody).eq ?_).mono (CoreSpec.coreCost_le L H m v Unode P)
  rw [← chain_val L (2 * m) hL H N.w0 N.w0_symm (N.w0_total hr) (flipF (Ktow L H) N.w0 N.F0), N.val_base hr]

end DominantStrings.Pseudo
