import OnePigeonhole.Pseudo.Helpers
import TransposeBase.Arith
import TransposeBase.Pseudo.CnfNet
import TransposeBase.Pseudo.FinalBrute
import TransposeBase.Pseudo.Place
import TransposeBase.Sat

/-! The fuel of the traversal, the brute force below `K ^ 2` variables, and the arithmetic of the final cost. -/

section

namespace OnePigeonhole.Pseudo.Final

open Finset TransposeBase General TransposeBase.Pseudo TransposeBase.Pseudo.Code
 OnePigeonhole.Pseudo.Leaf

theorem two_pow_clog_le {L : ℕ} (hL : 2 ≤ L) : 2 ^ Nat.clog 2 (3 * L) ≤ 6 * L := by
  have h1 : 1 < 3 * L := by omega
  have h2 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
  have h3 : 0 < Nat.clog 2 (3 * L) := Nat.clog_pos (by norm_num) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 (3 * L) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h3).symm⟩
  rw [hk] at h2 ⊢
  simp only [Nat.pred_succ] at h2
  rw [pow_succ]
  omega

/-- The arithmetic of the bound on the core. -/
theorem core_arith {q x2 x3 a b u v k l P D y : ℝ} (hq : 0 ≤ q) (hx2 : 0 ≤ x2) (hx3 : 1 ≤ x3)
    (ha0 : 0 ≤ a) (ha : a ≤ P) (hb0 : 0 ≤ b) (hb : b ≤ D) (hu0 : 0 ≤ u) (hu : u ≤ 34000 * y ^ 6) (hv0 : 0 ≤ v)
    (hv : v ≤ y) (hy : 1 ≤ y) (hP : 1 ≤ P) (hD : 1 ≤ D) (hk : 0 ≤ k) (hl : 0 ≤ l) :
    q * a * x2 * (k * b + l * x3 * (k * b + 2 * (u * v))) ≤
      (x2 * x3) * (q * (k + l * (k + 68000))) * (P * D * y ^ 7) := by
  have hy7 : 1 ≤ y ^ 7 := one_le_pow₀ hy
  have hP0 : 0 ≤ P := by linarith
  have hD0 : 0 ≤ D := by linarith
  have e7 : y ^ 7 = y ^ 6 * y := by ring
  generalize hy6 : y ^ 6 = y6 at *
  have hy60 : 0 ≤ y6 := by
    rw [← hy6]
    positivity
  have hkb0 : 0 ≤ k * b := by positivity
  set Z := P * D * y ^ 7 with hZ
  have a2 : a * (k * b) ≤ k * Z := by
    have s1 : a * (k * b) ≤ P * (k * D) := by gcongr
    have s3 : P * D ≤ Z := by
      rw [hZ]
      have : 0 ≤ P * D := by positivity
      nlinarith
    have : P * (k * D) = k * (P * D) := by ring
    rw [this] at s1
    have : k * (P * D) ≤ k * Z := mul_le_mul_of_nonneg_left s3 hk
    linarith
  have a3 : a * (2 * (u * v)) ≤ 68000 * Z := by
    have s1 : a * (2 * (u * v)) ≤ P * (2 * ((34000 * y6) * y)) := by gcongr
    have s2 : P * (2 * ((34000 * y6) * y)) = 68000 * (P * y ^ 7) := by
      rw [e7]
      ring
    have s3 : P * y ^ 7 ≤ Z := by
      have h1 : P ≤ P * D := by nlinarith
      rw [hZ]
      exact mul_le_mul_of_nonneg_right h1 (by linarith)
    rw [s2] at s1
    linarith
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    positivity
  have hmid : a * (k * b + l * x3 * (k * b + 2 * (u * v))) ≤ x3 * ((k + l * (k + 68000)) * Z) := by
    have e : a * (k * b + l * x3 * (k * b + 2 * (u * v))) =
        a * (k * b) + l * x3 * (a * (k * b) + a * (2 * (u * v))) := by ring
    rw [e]
    have hlx : 0 ≤ l * x3 := by positivity
    have s1 : l * x3 * (a * (k * b) + a * (2 * (u * v))) ≤ l * x3 * (k * Z + 68000 * Z) :=
      mul_le_mul_of_nonneg_left (add_le_add a2 a3) hlx
    have s2 : k * Z ≤ x3 * (k * Z) := by nlinarith [mul_nonneg hk hZ0]
    have e2 : x3 * ((k + l * (k + 68000)) * Z) = x3 * (k * Z) + l * x3 * (k * Z + 68000 * Z) := by ring
    rw [e2]
    linarith
  calc q * a * x2 * (k * b + l * x3 * (k * b + 2 * (u * v)))
      = q * x2 * (a * (k * b + l * x3 * (k * b + 2 * (u * v)))) := by ring
    _ ≤ q * x2 * (x3 * ((k + l * (k + 68000)) * Z)) := mul_le_mul_of_nonneg_left hmid (by positivity)
    _ = _ := by ring

end OnePigeonhole.Pseudo.Final

end

section

namespace OnePigeonhole.Pseudo.Final

open Finset TransposeBase General TransposeBase.Pseudo TransposeBase.Pseudo.Code
 SatBase OnePigeonhole.Pseudo.Leaf
  TransposeBase.Pseudo.CnfTree TransposeBase.Pseudo.CnfNet TransposeBase.Pseudo.Place

theorem exp_mono {l N M L : ℝ} (hl : 0 ≤ l) (hL : 0 < L) (h : N ≤ M) :
    Real.exp (9 * (l + 3) * N / L) ≤ Real.exp (9 * (l + 3) * M / L) := by
  refine Real.exp_le_exp.mpr ?_
  gcongr

theorem cost_real {o c ov : ℕ} {a x y q r : ℝ} (h1 : o ≤ ov + c) (h2 : (c : ℝ) ≤ a * x * q * r) (hxy : x ≤ y)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hr : 0 ≤ r) : (o : ℝ) ≤ (ov : ℝ) + a * y * q * r := by
  have h3 : (o : ℝ) ≤ (ov : ℝ) + c := by exact_mod_cast h1
  have h4 : a * x * q * r ≤ a * y * q * r := by gcongr
  linarith

end OnePigeonhole.Pseudo.Final

end

section

namespace OnePigeonhole.Pseudo.Final

open Finset SatBase TransposeBase TransposeBase.Sat TransposeBase.General TransposeBase.Pseudo
  TransposeBase.Pseudo.Final OnePigeonhole.Pseudo.Leaf
  TransposeBase.Pseudo.CnfTree TransposeBase.Pseudo.Place

/-- The fuel: `2 ^ (n / k + 2)`, on `root :: f :: n :: rest`. -/
def fuelE (k : ℕ) : Expr := .pow2 (.add (.div (.var 2) (.lit k)) (.lit 2))

theorem log_two_half : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]

theorem two_rpow_eq (x : ℝ) : (2 : ℝ) ^ x = Real.exp (Real.log 2 * x) :=
  Real.rpow_def_of_pos (by norm_num) x

/-- The fuel bounds twice the number of leaves. -/
theorem leaves_le_fuel {n ℓ k : ℕ} (hℓ : 2 ≤ ℓ) (hk : 0 < k)
    (hrate : (20 * Real.log ℓ + 10) / ℓ ≤ 1 / (2 * (k : ℝ))) (s : SparseState n ℓ) :
    2 * (sparseTree hℓ s).numLeaves ≤ 2 ^ (n / k + 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓ0 : (0 : ℝ) < ℓ := by
    have : 0 < ℓ := by omega
    exact_mod_cast this
  have hleaves := sparseTree_leaves hℓ s
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h1 : (20 * Real.log ℓ + 10) * n / ℓ ≤ (n : ℝ) / (2 * k) := by
    calc _ = ((20 * Real.log ℓ + 10) / ℓ) * n := by ring
      _ ≤ 1 / (2 * (k : ℝ)) * n := mul_le_mul_of_nonneg_right hrate hn0
      _ = _ := by ring
  have hdiv : (n : ℝ) / k ≤ ((n / k : ℕ) : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((n : ℝ) / k)
    rw [Nat.floor_div_eq_div] at h
    exact h.le
  have h2 : (n : ℝ) / (2 * k) ≤ Real.log 2 * (((n / k : ℕ) : ℝ) + 1) := by
    have h0 : 0 ≤ ((n : ℝ) / k) := by positivity
    have e : (n : ℝ) / (2 * k) = 1 / 2 * ((n : ℝ) / k) := by
      field_simp
    rw [e]
    have h3 : (1 : ℝ) / 2 * ((n : ℝ) / k) ≤ Real.log 2 * ((n : ℝ) / k) :=
      mul_le_mul_of_nonneg_right log_two_half h0
    have h4 : Real.log 2 * ((n : ℝ) / k) ≤ Real.log 2 * (((n / k : ℕ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hdiv (Real.log_nonneg (by norm_num))
    linarith
  have h3 : ((sparseTree hℓ s).numLeaves : ℝ) ≤ (2 : ℝ) ^ (n / k + 1) := by
    calc _ ≤ Real.exp ((20 * Real.log ℓ + 10) * n / ℓ) := hleaves
      _ ≤ Real.exp (Real.log 2 * (((n / k : ℕ) : ℝ) + 1)) := Real.exp_le_exp.mpr (h1.trans h2)
      _ = _ := by
        rw [mul_comm (Real.log 2), ← Nat.cast_succ, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h4 : (sparseTree hℓ s).numLeaves ≤ 2 ^ (n / k + 1) := by exact_mod_cast h3
  rw [pow_succ 2 (n / k + 1)]
  omega

/-- The fuel in real numbers. -/
theorem fuel_real {n k : ℕ} {ε : ℝ} (hk : 0 < k) (hkε : 1 / (k : ℝ) ≤ ε / 4) :
    ((2 ^ (n / k + 2) : ℕ) : ℝ) ≤ 4 * (2 : ℝ) ^ (ε / 4 * n) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h1 : ((n / k : ℕ) : ℝ) ≤ ε / 4 * n := by
    calc ((n / k : ℕ) : ℝ) ≤ (n : ℝ) / k := Nat.cast_div_le
      _ = 1 / (k : ℝ) * n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hkε hn0
  have h2 : (2 : ℝ) ^ (n / k) ≤ (2 : ℝ) ^ (ε / 4 * n) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  push_cast
  rw [pow_add]
  linarith

/-- The rate of the leaf. -/
theorem rate_real {L D n : ℕ} {ε : ℝ} (hL : 80 ≤ L) (hD : 1 ≤ D) (hε : 0 < ε)
    (h : 10 * (D : ℝ) ^ 2 * ((Real.log L + 2) / L) ≤ ε / 20) :
    Real.exp (9 * (Real.log L + 3) * ((4 * D * n : ℕ) : ℝ) / L) ≤ (2 : ℝ) ^ (ε / 2 * n) := by
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hlog0 : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have hr0 : 0 ≤ (Real.log L + 2) / L := by positivity
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hn0 : (0 : ℝ) ≤ n := by positivity
  set r := (Real.log L + 2) / L with hr
  have hr3 : (Real.log L + 3) / L ≤ 3 / 2 * r := by
    rw [hr, div_le_iff₀ hL0]
    have e : 3 / 2 * ((Real.log (L : ℝ) + 2) / L) * L = 3 / 2 * (Real.log L + 2) := by
      field_simp
    rw [e]
    linarith
  have e : 9 * (Real.log L + 3) * ((4 * D * n : ℕ) : ℝ) / L = 36 * (D : ℝ) * ((Real.log L + 3) / L) * n := by
    push_cast
    ring
  rw [e, two_rpow_eq]
  refine Real.exp_le_exp.mpr ?_
  have hDD : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
  have h1 : 36 * (D : ℝ) * ((Real.log L + 3) / L) ≤ 3 / 10 * ε := by
    have s1 : 36 * (D : ℝ) * ((Real.log L + 3) / L) ≤ 36 * (D : ℝ) * (3 / 2 * r) :=
      mul_le_mul_of_nonneg_left hr3 (by positivity)
    have s2 : (D : ℝ) * r ≤ (D : ℝ) ^ 2 * r := mul_le_mul_of_nonneg_right hDD hr0
    nlinarith
  have h2 : (3 : ℝ) / 10 * ε ≤ Real.log 2 * (ε / 2) := by
    have := Real.log_two_gt_d9
    nlinarith
  calc 36 * (D : ℝ) * ((Real.log L + 3) / L) * n ≤ Real.log 2 * (ε / 2) * n :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hn0
    _ = _ := by ring

/-- The bound on a leaf in the form of a constant, a power of `n + 1`, and the exponential. -/
theorem leaf_bound_real {Yc b0 n pk : ℕ} {L X E q : ℝ} (hYc : 1 ≤ Yc) (hb : 6 ≤ b0) (hL : 0 ≤ L) (hq : 0 ≤ q)
    (hX0 : 0 ≤ X) (hX : X ≤ E) (hE : 1 ≤ E) :
    ((100000 * (Yc * (n + 1)) ^ 6 + 4 * (pk * (Yc * (n + 1)) ^ 3) : ℕ) : ℝ) +
        L * X * q * (((Yc * (n + 1) : ℕ) : ℝ) ^ b0) ≤
      ((100000 + 4 * (pk : ℝ) + L * q) * (Yc : ℝ) ^ b0) * ((n : ℝ) + 1) ^ b0 * E := by
  have hY : (1 : ℝ) ≤ ((Yc * (n + 1) : ℕ) : ℝ) := by
    have : 1 ≤ Yc * (n + 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  set Y : ℝ := ((Yc * (n + 1) : ℕ) : ℝ) with hYdef
  have hpk : (0 : ℝ) ≤ pk := by positivity
  have e0 : ((100000 * (Yc * (n + 1)) ^ 6 + 4 * (pk * (Yc * (n + 1)) ^ 3) : ℕ) : ℝ) =
      100000 * Y ^ 6 + 4 * ((pk : ℝ) * Y ^ 3) := by
    rw [hYdef]
    push_cast
    ring
  have h6 : Y ^ 6 ≤ Y ^ b0 := pow_le_pow_right₀ hY hb
  have h3 : Y ^ 3 ≤ Y ^ b0 := pow_le_pow_right₀ hY (by omega)
  have hYb0 : 0 ≤ Y ^ b0 := by positivity
  have eY : Y ^ b0 = (Yc : ℝ) ^ b0 * ((n : ℝ) + 1) ^ b0 := by
    rw [hYdef]
    push_cast
    rw [mul_pow]
  rw [e0]
  have a1 : 100000 * Y ^ 6 + 4 * ((pk : ℝ) * Y ^ 3) ≤ (100000 + 4 * (pk : ℝ)) * Y ^ b0 := by
    have := mul_le_mul_of_nonneg_left h3 hpk
    nlinarith
  have a2 : (100000 + 4 * (pk : ℝ)) * Y ^ b0 ≤ (100000 + 4 * (pk : ℝ)) * Y ^ b0 * E := by
    have : 0 ≤ (100000 + 4 * (pk : ℝ)) * Y ^ b0 := by positivity
    nlinarith
  have a3 : L * X * q * Y ^ b0 ≤ L * E * q * Y ^ b0 := by gcongr
  calc _ ≤ (100000 + 4 * (pk : ℝ)) * Y ^ b0 * E + L * E * q * Y ^ b0 := by linarith
    _ = (100000 + 4 * (pk : ℝ) + L * q) * Y ^ b0 * E := by ring
    _ = _ := by
      rw [eY]
      ring

/-- The total. -/
theorem total_real {A U t E1 E2 E C2 c3 : ℝ} {F : ℝ} {b0 : ℕ} (hA : 1 ≤ A) (hE1 : 1 ≤ E1) (hE2 : 1 ≤ E2)
    (hE : E1 * E2 ≤ E) (hC2 : 0 ≤ C2) (hc3 : 0 ≤ c3) (hF : F ≤ 4 * E1) (hU0 : 0 ≤ U)
    (hU : U ≤ C2 * A ^ b0 * E2) (ht0 : 0 ≤ t) (ht : t ≤ c3 * A ^ 8) :
    9 + F * (U + t) + t ≤ (9 + 4 * C2 + 5 * c3) * A ^ (b0 + 8) * E := by
  have hA0 : (1 : ℝ) ≤ A ^ b0 := one_le_pow₀ hA
  have hA8 : (1 : ℝ) ≤ A ^ 8 := one_le_pow₀ hA
  have hAb : A ^ (b0 + 8) = A ^ b0 * A ^ 8 := pow_add _ _ _
  have hAA : A ^ b0 ≤ A ^ (b0 + 8) := pow_le_pow_right₀ hA (by omega)
  have hA88 : A ^ 8 ≤ A ^ (b0 + 8) := pow_le_pow_right₀ hA (by omega)
  have hP : 1 ≤ A ^ (b0 + 8) := one_le_pow₀ hA
  have hE10 : 0 ≤ E1 := by linarith
  have hE20 : 0 ≤ E2 := by linarith
  have hE' : 1 ≤ E := by nlinarith
  set P := A ^ (b0 + 8) with hPdef
  have u1 : U ≤ C2 * P * E2 := by
    refine hU.trans ?_
    gcongr
  have u2 : t ≤ c3 * P := by
    refine ht.trans ?_
    gcongr
  have s1 : F * (U + t) ≤ (4 * E1) * (C2 * P * E2 + c3 * P) := by
    refine mul_le_mul hF (by linarith) (by positivity) (by positivity)
  have hCP : 0 ≤ C2 * P := by positivity
  have hcP : 0 ≤ c3 * P := by positivity
  have s2 : (4 * E1) * (C2 * P * E2) ≤ 4 * (C2 * P) * E := by
    have e : (4 * E1) * (C2 * P * E2) = 4 * (C2 * P) * (E1 * E2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have s3 : (4 * E1) * (c3 * P) ≤ 4 * (c3 * P) * E := by
    have h1 : E1 ≤ E1 * E2 := by nlinarith
    have h2 := h1.trans hE
    nlinarith
  have s4 : t ≤ c3 * P * E := by nlinarith
  have s5 : (9 : ℝ) ≤ 9 * P * E := by nlinarith [mul_le_mul hP hE' (by norm_num) (by linarith : 0 ≤ P)]
  have e : (9 + 4 * C2 + 5 * c3) * P * E = 9 * P * E + 4 * (C2 * P) * E + 4 * (c3 * P) * E + c3 * P * E := by ring
  rw [e]
  have e2 : (4 * E1) * (C2 * P * E2 + c3 * P) = (4 * E1) * (C2 * P * E2) + (4 * E1) * (c3 * P) := by ring
  linarith

/-- The word of the formula is below `2 ^ W`. -/
theorem encF_lt_word {n c : ℕ} {F : ClauseSet (SignedLiteral n)} (hw : ∀ C ∈ F, C.card ≤ 3) (hc : 8 ≤ c) :
    encF n F < 2 ^ (c * (n + 1) ^ 3) := by
  have h1 : encF n F < 2 ^ cap n := encF_lt hw
  refine h1.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  exact (cap_le_pow n).trans (Nat.mul_le_mul_right _ hc)

/-- A small constant is below the bound. -/
theorem const_le_bound {x C' C A E : ℝ} {b : ℕ} (hx : x ≤ C') (hC' : 0 ≤ C') (hC : C' ≤ C) (hA : 1 ≤ A) (hE : 1 ≤ E) :
    x ≤ C * A ^ b * E := by
  have h1 : 1 ≤ A ^ b := one_le_pow₀ hA
  have h2 : 1 ≤ A ^ b * E := by nlinarith
  have h3 : 0 ≤ C := hC'.trans hC
  calc x ≤ C := hx.trans hC
    _ = C * 1 := by ring
    _ ≤ C * (A ^ b * E) := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := by ring

/-- The cost of `bruteE`. It depends only on `n`, and not on the word size or on the formula. -/
def bruteB (n : ℕ) : ℕ :=
  4 + 2 + 2 ^ n * (1 + 17 + cap n * (3 + 17 + (4 + 3 + 2 * n * (3 + 118 + 29 + 4)) + 1) + 4)

/-- The cost of exhaustive search, for every word size. -/
theorem bruteE_ops {W n : ℕ} (hC : CnfTree.Ctx W n) (f : ℕ) (rest : List ℕ) :
    ops W bruteE (f :: n :: rest) ≤ bruteB n := by
  have w := hC.one_le
  have w2 := hC.two_le
  have hcap := hC.cap_lt
  have hG := CnfTree.Ctx.G_le_cap n
  have h2lit : (2 : ℕ) < 2 ^ W := by
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hC.eight_le
  have hn : n < W := by omega
  have a0 : CnfTree.Run W (.pow2 (.var 1)) (f :: n :: rest) (2 ^ n) 2 :=
    run_pow2 (run_var (by simp)) hn
  have t := test_ex (N := 2 ^ n) (p := fun z => ∀ k < cap n, f.testBit k = false ∨
      ∃ c < 2 * n, InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2) w a0
    (fun z hz => test_all w (run_cap (nv := 2) hC (by simp)) (fun k hk => by
      have a1 := CnfNet.run_bitE w2 (f := 2) (i := 0) (env := k :: z :: f :: n :: rest) (fv' := f) (iv := k)
        (by simp) (by simp) (by omega)
      have t1 := test_eq w a1 (run_zero w)
      have e1 : (f.testBit k).toNat = 0 ↔ f.testBit k = false := by cases f.testBit k <;> simp
      have t2 := test_ex (N := 2 * n) (p := fun c => InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2)
        (B := 3 + 118 + 29) w (env := k :: z :: f :: n :: rest)
        (run_lits (nv := 3) hC (by simp)) (fun c hc => by
          have hn3 : (k :: z :: f :: n :: rest).getD 3 0 = n := by simp
          have t1 := test_inL (k := 1) (kv := k) hC hn3 hc (by simp)
          have a1 : CnfTree.Run W (.div (.var 0) (.lit 2)) (c :: k :: z :: f :: n :: rest) (c / 2) 3 :=
            run_div (run_var (by simp)) (run_lit h2lit)
          have a2 := CnfNet.run_bitE w2 (f := 3) (i := 0) (env := (c / 2) :: c :: k :: z :: f :: n :: rest)
            (fv' := z) (iv := c / 2) (by simp) (by simp) (by omega)
          have a3 := run_let a1 a2
          have a4 : CnfTree.Run W (.mod (.var 0) (.lit 2)) (c :: k :: z :: f :: n :: rest) (c % 2) 3 :=
            run_mod (run_var (by simp)) (run_lit h2lit)
          have t2 := test_eq w a3 a4
          exact test_and w t1 (fun _ => t2))
      exact (test_or w t1 (fun _ => t2)).iff (by rw [e1])))
  exact t.2

end OnePigeonhole.Pseudo.Final

end
