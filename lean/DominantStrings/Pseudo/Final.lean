import TransposeBase.Pseudo.FinalBrute
import DominantStrings.Pseudo.FinalLeaf
import TransposeBase.Arith
import TransposeBase.Sat

/-!
# The end-to-end theorem of the pseudocode layer

`Final.pseudo_main`: for every `ε > 0` there are one program `P`, constants `C`, `b`, `c`, such that for every `n` and
every 3-CNF `F` on `n` variables, with `W = c * (n + 1) ^ 3` and `env = [encF n F, n]`, the value of `P` is not zero
exactly when `F` is satisfiable, and `P` costs at most `C * (n + 1) ^ b * 2 ^ (ε * n)` word operations.

`P` is one fixed `Expr`, chosen after `ε` and before `n` and `F`. So `size P` and `stack P` are numbers that depend only on
`ε`, and no statement about them is needed: live words are at most `stack P` plus the environment, each of `W` bits.

`encF_lt_word`: the word `encF n F` of the input is below `2 ^ W`.

`Final.pseudo_wide` is the same statement for every word size `W ≥ c * (n + 1) ^ 3` and every environment that continues
below `encF n F :: n`, with the same `P` and the same bound. The machine layer uses it.

The parameters of the chain are `L = 2` and `H`, so the placement has `K = Ktow 2 H = 2 ^ 2 ^ H` words. `P = leafP d n`
bounds the potential of the first level, `EbD 2 H P i` bounds the ends on the words of one `u` at the depth `i`, and
`Ef H P` bounds the ends of the last level. The exponent `(∑ i ∈ range H, EbD 2 H P i) + Ef H P` of a leaf is at most
`chainRate (1 + d) H * n` (`exponent_le`), and `chainRate (1 + d) H` tends to `0` as `H` tends to infinity (`exists_rate`).
Up to `K ^ 2` variables the program tries all assignments.
-/

namespace DominantStrings.Pseudo.Final

open Finset SatBase TransposeBase TransposeBase.Sat TransposeBase.General TransposeBase.Pseudo
  TransposeBase.Pseudo.Final TransposeBase.Pseudo.Leaf
  TransposeBase.Pseudo.CnfTree

/-! ### The arithmetic of the parameters -/

/-- The fuel: `2 ^ (n / k + 2)`, on `root :: f :: n :: rest`. -/
def fuelE (k : ℕ) : Expr := .pow2 (.add (.div (.var 2) (.lit k)) (.lit 2))

theorem log_two_half : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]

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

/-! ### The input word -/

/-- The word of the formula is below `2 ^ W`. -/
theorem encF_lt_word {n c : ℕ} {F : ClauseSet (SignedLiteral n)} (hw : ∀ C ∈ F, C.card ≤ 3) (hc : 8 ≤ c) :
    encF n F < 2 ^ (c * (n + 1) ^ 3) := by
  have h1 : encF n F < 2 ^ cap n := encF_lt hw
  refine h1.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
  exact (cap_le_pow n).trans (Nat.mul_le_mul_right _ hc)

/-! ### The top program -/

/-- The top program: exhaustive search up to `n₀` variables, and the branching tree above. -/
def topE (n₀ k ℓ H : ℕ) : Expr :=
  .ite (.var 1) (.lit n₀) bruteE (treeE ℓ (fuelE k) (leafE 2 H))

theorem eval_topE {W n₀ k ℓ H n w : ℕ} {rest : List ℕ} (h : n₀ < 2 ^ W) :
    eval W (topE n₀ k ℓ H) (w :: n :: rest) =
      if n ≤ n₀ then eval W bruteE (w :: n :: rest)
      else eval W (treeE ℓ (fuelE k) (leafE 2 H)) (w :: n :: rest) := by
  have h1 : eval W (.lit n₀) (w :: n :: rest) = n₀ := eval_lit_small W h
  show (if eval W (.var 1) (w :: n :: rest) ≤ eval W (.lit n₀) (w :: n :: rest) then _ else _) = _
  rw [h1]
  rfl

theorem ops_topE {W n₀ k ℓ H n w : ℕ} {rest : List ℕ} (h : n₀ < 2 ^ W) :
    ops W (topE n₀ k ℓ H) (w :: n :: rest) =
      3 + if n ≤ n₀ then ops W bruteE (w :: n :: rest)
        else ops W (treeE ℓ (fuelE k) (leafE 2 H)) (w :: n :: rest) := by
  have h1 : eval W (.lit n₀) (w :: n :: rest) = n₀ := eval_lit_small W h
  show 1 + 1 + 1 + (if eval W (.var 1) (w :: n :: rest) ≤ eval W (.lit n₀) (w :: n :: rest) then _ else _) = _
  rw [h1]
  rfl

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

/-! ### Exhaustive search: an explicit cost -/

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
    CnfTree.run_pow2 (CnfTree.run_var (by simp)) hn
  have t := CnfTree.test_ex (N := 2 ^ n) (p := fun z => ∀ k < cap n, f.testBit k = false ∨
      ∃ c < 2 * n, InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2) w a0
    (fun z hz => CnfTree.test_all w (CnfTree.run_cap (nv := 2) hC (by simp)) (fun k hk => by
      have a1 := CnfNet.run_bitE w2 (f := 2) (i := 0) (env := k :: z :: f :: n :: rest) (fv' := f) (iv := k)
        (by simp) (by simp) (by omega)
      have t1 := CnfTree.test_eq w a1 (CnfTree.run_zero w)
      have e1 : (f.testBit k).toNat = 0 ↔ f.testBit k = false := by cases f.testBit k <;> simp
      have t2 := CnfTree.test_ex (N := 2 * n) (p := fun c => InC n (c + 1) k ∧ (z.testBit (c / 2)).toNat = c % 2)
        (B := 3 + 118 + 29) w (env := k :: z :: f :: n :: rest)
        (CnfTree.run_lits (nv := 3) hC (by simp)) (fun c hc => by
          have hn3 : (k :: z :: f :: n :: rest).getD 3 0 = n := by simp
          have t1 := CnfTree.test_inL (k := 1) (kv := k) hC hn3 hc (by simp)
          have a1 : CnfTree.Run W (.div (.var 0) (.lit 2)) (c :: k :: z :: f :: n :: rest) (c / 2) 3 :=
            CnfTree.run_div (CnfTree.run_var (by simp)) (CnfTree.run_lit h2lit)
          have a2 := CnfNet.run_bitE w2 (f := 3) (i := 0) (env := (c / 2) :: c :: k :: z :: f :: n :: rest)
            (fv' := z) (iv := c / 2) (by simp) (by simp) (by omega)
          have a3 := CnfTree.run_let a1 a2
          have a4 : CnfTree.Run W (.mod (.var 0) (.lit 2)) (c :: k :: z :: f :: n :: rest) (c % 2) 3 :=
            CnfTree.run_mod (CnfTree.run_var (by simp)) (CnfTree.run_lit h2lit)
          have t2 := CnfTree.test_eq w a3 a4
          exact CnfTree.test_and w t1 (fun _ => t2))
      exact (CnfTree.test_or w t1 (fun _ => t2)).iff (by rw [e1])))
  exact t.2

/-! ### The exponent of a leaf

Here `L = 2`, and `P ≤ (6 * M) ^ 2` bounds the potential of the first level. At the depth `i`, let `j = H - (i + 1)`. The step
has `Kd 2 H (i + 1) = Ktow 2 j ≥ 4 ^ j` words on a side, so `EbD 2 H P i ≤ 12 * M * (477 / 500) ^ H * (21 / 40) ^ (j + 1)`
(`EbD_le_real`). The proof uses two numeric facts in place of the square root of `91 / 100`: `91 ≤ 100 * (477 / 500) ^ 2` and
`1 ≤ 4 * (477 / 500) ^ 2 * (21 / 40) ^ 2`. The sum over the depths is a geometric sum (`sum_geom_le`). -/

theorem two_mul_le_two_pow (j : ℕ) : 2 * j ≤ 2 ^ j := by
  cases j with
  | zero => simp
  | succ i =>
    have h : i < 2 ^ i := Nat.lt_two_pow_self
    rw [pow_succ]
    omega

/-- The number of words at height `j` is at least `4 ^ j`, for `L = 2`. -/
theorem four_pow_le_Ktow (j : ℕ) : 4 ^ j ≤ Ktow 2 j := by
  rw [Ktow_eq, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (two_mul_le_two_pow j)

theorem le_of_sq_mul_le {E Z y : ℝ} (hE : 0 ≤ E) (hy : 0 ≤ y) (hZ : 0 < Z) (h : E ^ 2 * Z ≤ y ^ 2 * Z) : E ≤ y :=
  (pow_le_pow_iff_left₀ hE hy (by norm_num)).mp (le_of_mul_le_mul_right h hZ)

theorem sq_mul_eq (M g r : ℝ) (i j : ℕ) :
    (12 * M * g ^ (i + j + 1) * r ^ (j + 1)) ^ 2 * (100 ^ i * 4 ^ j) =
      36 * M ^ 2 * (100 * g ^ 2) ^ i * (4 * g ^ 2 * r ^ 2) ^ j * (4 * g ^ 2 * r ^ 2) := by
  ring

/-- The bound on the ends of one row at the depth `i`, where `H - i` steps remain. -/
theorem EbD_le_real {H i P M : ℕ} (hi : i < H) (hP : P ≤ (6 * M) ^ 2) :
    ((EbD 2 H P i : ℕ) : ℝ) ≤ 12 * (M : ℝ) * (477 / 500) ^ H * (21 / 40) ^ (H - i) := by
  obtain ⟨j, rfl⟩ : ∃ j, H = i + j + 1 := ⟨H - (i + 1), by omega⟩
  have hk : i + j + 1 - i = j + 1 := by omega
  have hKd : 4 ^ j ≤ Kd 2 (i + j + 1) (i + 1) := by
    have e : i + j + 1 - (i + 1) = j := by omega
    rw [Kd, e]
    exact four_pow_le_Ktow j
  have h1 : EbD 2 (i + j + 1) P i ^ 2 * (100 ^ i * Kd 2 (i + j + 1) (i + 1)) ≤ 91 ^ i * P :=
    (Nat.mul_le_mul_right _ (Nat.sqrt_le' _)).trans (Nat.div_mul_le_self _ _)
  rw [hk]
  generalize EbD 2 (i + j + 1) P i = E at h1 ⊢
  generalize Kd 2 (i + j + 1) (i + 1) = K' at h1 hKd
  have h3 : E ^ 2 * (100 ^ i * 4 ^ j) ≤ 91 ^ i * (36 * M ^ 2) := by
    calc E ^ 2 * (100 ^ i * 4 ^ j) ≤ E ^ 2 * (100 ^ i * K') := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hKd)
      _ ≤ 91 ^ i * P := h1
      _ ≤ 91 ^ i * (6 * M) ^ 2 := Nat.mul_le_mul_left _ hP
      _ = 91 ^ i * (36 * M ^ 2) := by ring
  have h4 : (E : ℝ) ^ 2 * (100 ^ i * 4 ^ j) ≤ 91 ^ i * (36 * (M : ℝ) ^ 2) := by exact_mod_cast h3
  refine le_of_sq_mul_le (Nat.cast_nonneg _) (by positivity) (by positivity) (h4.trans ?_)
  rw [sq_mul_eq]
  have a1 : (91 : ℝ) ^ i ≤ (100 * (477 / 500) ^ 2) ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
  have a2 : (1 : ℝ) ≤ (4 * (477 / 500) ^ 2 * (21 / 40) ^ 2) ^ j := one_le_pow₀ (by norm_num)
  have a3 : (1 : ℝ) ≤ 4 * (477 / 500) ^ 2 * (21 / 40) ^ 2 := by norm_num
  have a4 : (1 : ℝ) ≤ (4 * (477 / 500) ^ 2 * (21 / 40) ^ 2) ^ j * (4 * (477 / 500) ^ 2 * (21 / 40) ^ 2) :=
    one_le_mul_of_one_le_of_one_le a2 a3
  have hM0 : (0 : ℝ) ≤ 36 * (M : ℝ) ^ 2 := by positivity
  calc (91 : ℝ) ^ i * (36 * (M : ℝ) ^ 2)
      ≤ (100 * (477 / 500) ^ 2) ^ i * (36 * (M : ℝ) ^ 2) := mul_le_mul_of_nonneg_right a1 hM0
    _ = 36 * (M : ℝ) ^ 2 * (100 * (477 / 500) ^ 2) ^ i * 1 := by ring
    _ ≤ 36 * (M : ℝ) ^ 2 * (100 * (477 / 500) ^ 2) ^ i *
        ((4 * (477 / 500) ^ 2 * (21 / 40) ^ 2) ^ j * (4 * (477 / 500) ^ 2 * (21 / 40) ^ 2)) :=
        mul_le_mul_of_nonneg_left a4 (by positivity)
    _ = _ := by ring

/-- The bound on the ends of the last level. -/
theorem Ef_le_real {H P M : ℕ} (hP : P ≤ (6 * M) ^ 2) :
    ((Ef H P : ℕ) : ℝ) ≤ 6 * (M : ℝ) * (477 / 500) ^ H := by
  have h1 : Ef H P ^ 2 * 100 ^ H ≤ 91 ^ H * P :=
    (Nat.mul_le_mul_right _ (Nat.sqrt_le' _)).trans (Nat.div_mul_le_self _ _)
  generalize Ef H P = E at h1 ⊢
  have h3 : E ^ 2 * 100 ^ H ≤ 91 ^ H * (36 * M ^ 2) := by
    calc E ^ 2 * 100 ^ H ≤ 91 ^ H * P := h1
      _ ≤ 91 ^ H * (6 * M) ^ 2 := Nat.mul_le_mul_left _ hP
      _ = 91 ^ H * (36 * M ^ 2) := by ring
  have h4 : (E : ℝ) ^ 2 * 100 ^ H ≤ 91 ^ H * (36 * (M : ℝ) ^ 2) := by exact_mod_cast h3
  refine le_of_sq_mul_le (Nat.cast_nonneg _) (by positivity) (by positivity) (h4.trans ?_)
  have a1 : (91 : ℝ) ^ H ≤ (100 * (477 / 500) ^ 2) ^ H := pow_le_pow_left₀ (by norm_num) (by norm_num) H
  have e : (6 * (M : ℝ) * (477 / 500) ^ H) ^ 2 * 100 ^ H = (100 * (477 / 500) ^ 2) ^ H * (36 * (M : ℝ) ^ 2) := by
    generalize ((477 : ℝ) / 500) = g
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right a1 (by positivity)

/-- The geometric sum over the depths. -/
theorem sum_geom_le (H : ℕ) : ∑ i ∈ range H, ((21 : ℝ) / 40) ^ (H - i) ≤ 21 / 19 := by
  induction H with
  | zero =>
    rw [sum_range_zero]
    norm_num
  | succ H ih =>
    rw [sum_range_succ]
    have e : ∑ i ∈ range H, ((21 : ℝ) / 40) ^ (H + 1 - i) = 21 / 40 * ∑ i ∈ range H, ((21 : ℝ) / 40) ^ (H - i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have h : H + 1 - i = (H - i) + 1 := by
        have := mem_range.mp hi
        omega
      rw [h, pow_succ, mul_comm]
    rw [e, show H + 1 - H = 1 by omega, pow_one]
    linarith

/-- The exponent of a leaf per variable, for the constant `D = 1 + d`. -/
noncomputable def chainRate (D H : ℕ) : ℝ := 366 / 19 * (D : ℝ) * (477 / 500) ^ H

/-- **The exponent of a leaf.** -/
theorem exponent_le (D H n : ℕ) :
    (((∑ i ∈ range H, EbD 2 H (28 * (D * n) ^ 2) i) + Ef H (28 * (D * n) ^ 2) : ℕ) : ℝ) ≤ chainRate D H * n := by
  set M := D * n with hM
  have hP : 28 * M ^ 2 ≤ (6 * M) ^ 2 := by
    have e : (6 * M) ^ 2 = 36 * M ^ 2 := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ (by norm_num)
  have h1 : ∑ i ∈ range H, ((EbD 2 H (28 * M ^ 2) i : ℕ) : ℝ) ≤
      ∑ i ∈ range H, 12 * (M : ℝ) * (477 / 500) ^ H * (21 / 40) ^ (H - i) :=
    sum_le_sum fun i hi => EbD_le_real (mem_range.mp hi) hP
  have h2 : ∑ i ∈ range H, 12 * (M : ℝ) * (477 / 500) ^ H * ((21 : ℝ) / 40) ^ (H - i) ≤
      12 * (M : ℝ) * (477 / 500) ^ H * (21 / 19) := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_geom_le H) (by positivity)
  have h3 := Ef_le_real (H := H) hP
  have e : chainRate D H * n = 12 * (M : ℝ) * (477 / 500) ^ H * (21 / 19) + 6 * (M : ℝ) * (477 / 500) ^ H := by
    rw [hM]
    simp only [chainRate]
    push_cast
    ring
  rw [e]
  push_cast
  linarith

/-- **The choice of the parameter of the chain.** The rate tends to `0`. -/
theorem exists_rate (D : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ H : ℕ, chainRate D H ≤ ε := by
  have h1 : Filter.Tendsto (fun H : ℕ => ((477 : ℝ) / 500) ^ H) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h3 : Filter.Tendsto (chainRate D) Filter.atTop (nhds (366 / 19 * (D : ℝ) * 0)) := h1.const_mul _
  rw [mul_zero] at h3
  obtain ⟨H, hH⟩ := (h3.eventually (Iio_mem_nhds hε)).exists
  exact ⟨H, le_of_lt hH⟩

/-! ### Many variables -/

/-- **Many variables: the branching tree decides `F`.** All sizes are hypotheses, on an opaque word size `W`. -/
theorem large_case {ε : ℝ} (hε : 0 < ε) {k ℓ d H A W n : ℕ}
    (hA : ∀ {W m v Unode P : ℕ} {f : Frm} {N : BaseNet m v} {nodeG : ℕ → Expr},
      CoreOK W f 2 H N nodeG Unode P →
      RunZ W (coreE 2 H nodeG) f.list.tail
        (2 ^ scaleTot 2 (2 * m) H * ∑ z : Fin m → Bool, ∏ α, N.φ α (fun e => z e.1))
        (A * (m + v + 1) ^ 3 * (Unode + 1) * 2 ^ ((∑ i ∈ range H, EbD 2 H P i) + Ef H P)))
    (hk : 0 < k) (hkε : 1 / (k : ℝ) ≤ ε / 4) (hℓ : 2 ≤ ℓ)
    (hℓrate : (20 * Real.log ℓ + 10) / ℓ ≤ 1 / (2 * (k : ℝ))) (hd : d = 4 * ℓ ^ 2) (hd3 : 3 ≤ d)
    (hrate : (((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n) : ℕ) : ℝ) ≤ ε / 2 * n)
    (hth : Ktow 2 H ^ 2 ≤ n)
    (hW1 : (48 + (2 * d + Ktow 2 H + 12) ^ 2) * (n + 1) ^ 3 ≤ W)
    (hW2 : ((Ktow 2 H + 1) ^ 4 + chainBits 2 H + 16 * (1 + d) + 9) * (n + 1) ^ 3 ≤ W)
    (hW3 : ((2 * (1 + d) + 2) ^ 3 + 1) * (n + 1) ^ 3 ≤ W)
    (hW4 : (2 * (1 + d) * nRectTot 2 H + 1) * (n + 1) ^ 3 ≤ W)
    (hT : TreeCtx W n ℓ) (hkW : k < W)
    (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3) (rest : List ℕ) :
    (eval W (treeE ℓ (fuelE k) (leafE 2 H)) (encF n F :: n :: rest) ≠ 0 ↔
      ∃ x, holdsFormula (literalHolds x) F) ∧
    ((3 + ops W (treeE ℓ (fuelE k) (leafE 2 H)) (encF n F :: n :: rest) : ℕ) : ℝ) ≤
      (9 + 4 * (leafC (Ktow 2 H) d A : ℝ) + 5 * ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ)) *
        ((n : ℝ) + 1) ^ (9 + 8) * (2 : ℝ) ^ (ε * n) := by
  have hA1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hCtx := hT.ctx
  have hWpow : ∀ {x : ℕ}, x < W → x < 2 ^ W := fun h => h.trans Nat.lt_two_pow_self
  have hC20 : (0 : ℝ) ≤ (leafC (Ktow 2 H) d A : ℝ) := Nat.cast_nonneg _
  -- the bound for one leaf
  set E2 : ℝ := (2 : ℝ) ^ (ε / 2 * n) with hE2
  have hE21 : 1 ≤ E2 := Real.one_le_rpow (by norm_num) (by positivity)
  set B : ℝ := (leafC (Ktow 2 H) d A : ℝ) * ((n : ℝ) + 1) ^ 9 * E2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hexp : (2 : ℝ) ^ ((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n)) ≤ E2 := by
    rw [hE2, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hrate
  have hleaf : ∀ t, Reach hℓ (initialSparseState F hw ℓ hℓ) t → ∀ p,
      let E := encF n t.formula :: p :: encF n (initialSparseState F hw ℓ hℓ).formula :: encF n F :: n :: rest
      (eval W (leafE 2 H) E ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) t.formula) ∧
        ops W (leafE 2 H) E ≤ ⌊B⌋₊ := by
    intro t ht p E
    have hdeg : ∀ v, variableOccurrences t.formula v ≤ d := fun v => by
      rw [hd]
      exact noSparseRule_variable_bound t.formula ℓ hℓ t.width ht.isLeaf v
    obtain ⟨h1, h2⟩ := leaf_main hA le_rfl (G := t.formula) t.width hd3 hdeg hth hW1 hW2 hW3 hW4
      p (encF n (initialSparseState F hw ℓ hℓ).formula) (encF n F) rest
    refine ⟨h1, Nat.le_floor ?_⟩
    have h3 : ((ops W (leafE 2 H) E : ℕ) : ℝ) ≤ (leafC (Ktow 2 H) d A : ℝ) * ((n : ℝ) + 1) ^ 9 *
        (2 : ℝ) ^ ((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n)) := by
      exact_mod_cast h2
    exact h3.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  -- the fuel
  have hW8 : 8 ≤ W := hCtx.eight_le
  have h2 : (2 : ℕ) < 2 ^ W := by
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW8
  have hG := Ctx.G_le_cap n
  have hcap := hCtx.cap_lt
  have hdivle : n / k ≤ n := Nat.div_le_self _ _
  have hcap2 : 2 * n + 1 < W := by omega
  have hfuelLt : n / k + 2 < W := by omega
  have hfuelRun : ∀ root : ℕ, CnfTree.Run W (fuelE k) (root :: encF n F :: n :: rest) (2 ^ (n / k + 2)) 6 := fun root =>
    CnfTree.run_pow2 (CnfTree.run_add (CnfTree.run_div (CnfTree.run_var (i := 2) (v := n) rfl) (CnfTree.run_lit (hWpow hkW))) (CnfTree.run_lit h2) (hWpow hfuelLt)) hfuelLt
  have hf2 : 2 ^ (n / k + 2) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hfuelLt
  obtain ⟨hV, hO⟩ := treeE_correct (rest := rest) hT hℓ F hw (hfuelRun _).1
    (leaves_le_fuel hℓ hk hℓrate _) hf2 hleaf
  refine ⟨hV, ?_⟩
  have hfops := (hfuelRun (encF n (initialSparseState F hw ℓ hℓ).formula)).2
  have hnat : 3 + ops W (treeE ℓ (fuelE k) (leafE 2 H)) (encF n F :: n :: rest) ≤
      9 + 2 ^ (n / k + 2) * (⌊B⌋₊ + treeP ℓ n) + treeP ℓ n := by omega
  have hcast : ((3 + ops W (treeE ℓ (fuelE k) (leafE 2 H)) (encF n F :: n :: rest) : ℕ) : ℝ) ≤
      9 + ((2 ^ (n / k + 2) : ℕ) : ℝ) * ((⌊B⌋₊ : ℝ) + (treeP ℓ n : ℝ)) + (treeP ℓ n : ℝ) := by
    exact_mod_cast hnat
  set E1 : ℝ := (2 : ℝ) ^ (ε / 4 * n) with hE1
  have hE11 : 1 ≤ E1 := Real.one_le_rpow (by norm_num) (by positivity)
  have hEE : E1 * E2 ≤ (2 : ℝ) ^ (ε * n) := by
    rw [hE1, hE2, ← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (0 : ℝ) ≤ ε * n := by positivity
    linarith
  have htreeP : (treeP ℓ n : ℝ) = ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ 8 := by
    simp only [treeP]
    push_cast
    ring
  have hc30 : (0 : ℝ) ≤ ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ) = c3 at htreeP hc30 ⊢
  exact hcast.trans (total_real (C2 := (leafC (Ktow 2 H) d A : ℝ)) (c3 := c3) (b0 := 9) hA1 hE11 hE21 hEE hC20 hc30
    (fuel_real (n := n) hk hkε) (U := (⌊B⌋₊ : ℝ)) (Nat.cast_nonneg _) (Nat.floor_le hB0)
    (t := (treeP ℓ n : ℝ)) (Nat.cast_nonneg _) htreeP.le)

/-! ### The theorem -/

set_option linter.unusedVariables false in
/-- **The pseudocode theorem for every large word size.** The program `P` and the constants `C`, `b`, `c` are as in
`pseudo_core`. The word size `W` may be any number at least `c * (n + 1) ^ 3`, and the environment may continue below
`encF n F :: n` with any words `rest`. The bound on the operations depends on neither `W` nor `rest`. -/
theorem pseudo_wide (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Expr) (C : ℝ) (b c : ℕ), 8 ≤ c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3)
      (W : ℕ) (rest : List ℕ), c * (n + 1) ^ 3 ≤ W →
      let env := encF n F :: n :: rest
      (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
      (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n) := by
  classical
  -- the parameters
  obtain ⟨k, hk, hkε⟩ : ∃ k : ℕ, 0 < k ∧ 1 / (k : ℝ) ≤ ε / 4 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
    have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
    refine ⟨k, by exact_mod_cast hk0, ?_⟩
    rw [div_le_iff₀ hk0]
    rw [div_lt_iff₀ hε] at hk
    linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨ℓ, hℓ, hℓrate⟩ := exists_ell (ε := 2 / (k : ℝ)) (by positivity)
  have hℓrate' : (20 * Real.log ℓ + 10) / ℓ ≤ 1 / (2 * (k : ℝ)) := by
    refine hℓrate.trans (le_of_eq ?_)
    field_simp
    norm_num
  obtain ⟨d, hd⟩ : ∃ d, d = 4 * ℓ ^ 2 := ⟨_, rfl⟩
  have hd3 : 3 ≤ d := by
    have : 2 ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ 2
    omega
  obtain ⟨H, htrate⟩ := exists_rate (1 + d) (ε := ε / 2) (by positivity)
  have hrate : ∀ n : ℕ, (((∑ i ∈ range H, EbD 2 H (leafP d n) i) + Ef H (leafP d n) : ℕ) : ℝ) ≤ ε / 2 * n := fun n =>
    (exponent_le (1 + d) H n).trans (mul_le_mul_of_nonneg_right htrate (Nat.cast_nonneg _))
  obtain ⟨A, hA⟩ := core_spec 2 H
  -- the program and the constants
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = Ktow 2 H ^ 2 := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a1, a1 = 48 + (2 * d + Ktow 2 H + 12) ^ 2 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2, a2 = (Ktow 2 H + 1) ^ 4 + chainBits 2 H + 16 * (1 + d) + 9 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a3, a3 = (2 * (1 + d) + 2) ^ 3 + 1 := ⟨_, rfl⟩
  obtain ⟨a4, ha4⟩ : ∃ a4, a4 = 2 * (1 + d) * nRectTot 2 H + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 8 + (10 * ℓ + 3) + (ℓ * ℓ + 1) + (n₀ + 1) + (k + 1) + a1 + a2 + a3 + a4 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℕ, C1 = (range (n₀ + 1)).sup bruteB := ⟨_, rfl⟩
  obtain ⟨C3, hC3⟩ : ∃ C3 : ℝ, C3 = 9 + 4 * (leafC (Ktow 2 H) d A : ℝ) + 5 * ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hC30 : 0 ≤ C3 := by
    rw [hC3]
    positivity
  have hC10 : (0 : ℝ) ≤ C1 := Nat.cast_nonneg _
  refine ⟨topE n₀ k ℓ H, (C1 : ℝ) + 3 + C3, 9 + 8, c, by omega, ?_⟩
  intro n F hw W rest hcWn
  have hsup : n ≤ n₀ → bruteB n ≤ C1 := fun hn => by
    rw [hC1]
    exact Finset.le_sup (f := bruteB) (mem_range.mpr (Nat.lt_succ_of_le hn))
  have hA3 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hcW : ∀ x, x ≤ c → x * (n + 1) ^ 3 ≤ W := fun x hx => (Nat.mul_le_mul_right _ hx).trans hcWn
  have hcleW : c ≤ W := (Nat.le_mul_of_pos_right _ hA3).trans hcWn
  have hCtx0 : (2 * n + 2) ^ 3 ≤ W := by
    have e : (2 * n + 2) ^ 3 = 8 * (n + 1) ^ 3 := by ring
    rw [e]
    exact hcW 8 (by omega)
  have hdepth0 : 10 * n * ℓ + 3 ≤ W := by
    have h1 := hcW (10 * ℓ + 3) (by omega)
    have h2 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 : (10 * ℓ + 3) * (n + 1) ≤ (10 * ℓ + 3) * (n + 1) ^ 3 := Nat.mul_le_mul_left _ h2
    have e : (10 * ℓ + 3) * (n + 1) = 10 * n * ℓ + 10 * ℓ + 3 * n + 3 := by ring
    omega
  have hW1 := hcW a1 (by omega)
  have hW2 := hcW a2 (by omega)
  have hW3 := hcW a3 (by omega)
  have hW4 := hcW a4 (by omega)
  rw [ha1] at hW1
  rw [ha2] at hW2
  rw [ha3] at hW3
  rw [ha4] at hW4
  dsimp only
  have hWpow : W < 2 ^ W := Nat.lt_two_pow_self
  have hCtx : Ctx W n := ⟨hCtx0⟩
  have hn₀lt : n₀ < 2 ^ W := by omega
  have hA1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (ε * n) := Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hn : n ≤ n₀
  · -- few variables: exhaustive search
    refine ⟨?_, ?_⟩
    · rw [eval_topE hn₀lt, if_pos hn, bruteE_eval hCtx hw rest, ind_ne_zero]
    · rw [ops_topE hn₀lt, if_pos hn]
      refine const_le_bound (C' := (C1 : ℝ) + 3) ?_ (by positivity) (by linarith) hA1 hE
      have : 3 + ops W bruteE (encF n F :: n :: rest) ≤ C1 + 3 := by
        have := hsup hn
        have := bruteE_ops (W := W) (n := n) hCtx (encF n F) rest
        omega
      exact_mod_cast this
  · -- many variables: the branching tree
    have hnge : n₀ < n := not_le.mp hn
    have hth : Ktow 2 H ^ 2 ≤ n := by omega
    have hT : TreeCtx W n ℓ := ⟨hCtx, hdepth0, by omega⟩
    obtain ⟨h1, h2⟩ := large_case hε hA hk hkε hℓ hℓrate' hd hd3 (hrate n) hth hW1 hW2 hW3 hW4 hT
      (by omega) F hw rest
    refine ⟨?_, ?_⟩
    · rw [eval_topE hn₀lt, if_neg hn]
      exact h1
    · rw [ops_topE hn₀lt, if_neg hn]
      rw [← hC3] at h2
      refine h2.trans ?_
      have hP : 0 ≤ ((n : ℝ) + 1) ^ (9 + 8) := by positivity
      have hEP : 0 ≤ (2 : ℝ) ^ (ε * n) := by positivity
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hP) hEP
      linarith

set_option linter.unusedVariables false in
/-- The pseudocode theorem without the statement that the input consists of words. -/
theorem pseudo_core (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Expr) (C : ℝ) (b c : ℕ), 8 ≤ c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3),
      let W := c * (n + 1) ^ 3
      let env := [encF n F, n]
      (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
      (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n) := by
  obtain ⟨P, C, b, c, hc, h⟩ := pseudo_wide ε hε
  exact ⟨P, C, b, c, hc, fun n F hw => h n F hw _ [] le_rfl⟩

set_option linter.unusedVariables false in
/-- **The pseudocode theorem.** For every `ε > 0` there are one program `P`, constants `C`, `b`, `c`, with `c > 0`,
such that for every `n` and every formula `F` with `n` variables and clauses of at most three literals, with
`W = c * (n + 1) ^ 3` and `env = [encF n F, n]`, the input consists of words, the value of `P` is not zero exactly when
`F` is satisfiable, and the number of word operations is at most `C * (n + 1) ^ b * 2 ^ (ε * n)`.

By `eval_lt_word`, every value is then a word. `P` is chosen before `n` and `F`, so `size P` and `stack P` depend only
on `ε`. That `stack P` bounds the live words is the definition of `stack`, and no theorem here uses it; the compiler to
a machine must prove it. -/
theorem pseudo_main (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Expr) (C : ℝ) (b c : ℕ), 0 < c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3),
      let W := c * (n + 1) ^ 3
      let env := [encF n F, n]
      (encF n F < 2 ^ W ∧ n < 2 ^ W) ∧
      (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
      (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n) := by
  obtain ⟨P, C, b, c, hc, h⟩ := pseudo_core ε hε
  refine ⟨P, C, b, c, by omega, fun n F hw => ⟨⟨encF_lt_word hw hc, ?_⟩, h n F hw⟩⟩
  refine lt_of_le_of_lt ?_ Nat.lt_two_pow_self
  have h1 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h2 : (n + 1) ^ 3 ≤ c * (n + 1) ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
  omega

end DominantStrings.Pseudo.Final
