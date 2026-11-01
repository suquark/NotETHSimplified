import TransposeBase.Pseudo.CnfRun

/-!
# Clause tests and the normalization program

All programs read `n` from the variable `nv` and clause codes and formula words from variables.
-/

namespace TransposeBase.Pseudo.CnfTree

open SatBase Finset

variable {W : ℕ} {env : List ℕ} {n nv : ℕ}

def d0E (k nv : ℕ) : Expr := .mod (.var k) (gE nv)
def d1E (k nv : ℕ) : Expr := .mod (.div (.var k) (gE nv)) (gE nv)
def d2E (k nv : ℕ) : Expr := .mod (.div (.div (.var k) (gE nv)) (gE nv)) (gE nv)

/-- Is the value of `c` a digit of the code in the variable `k`? -/
def inE (c : Expr) (k nv : ℕ) : Expr :=
  tOr (tEq c (d0E k nv)) (tOr (tEq c (d1E k nv)) (tEq c (d2E k nv)))

/-- The literal code `c + 1`, for the loop variable `c`. -/
def cE : Expr := .add (.var 0) (.lit 1)

/-- Is the literal code `c + 1` a digit of the code in the variable `k`? -/
def inLE (k nv : ℕ) : Expr := inE cE k nv

/-- `decode j ⊆ decode k`, by a loop over the literal codes. -/
def subE (j k nv : ℕ) : Expr :=
  tAll (litsE nv) (tOr (tNot (inLE (j + 1) (nv + 1))) (inLE (k + 1) (nv + 1)))

/-- `decode j ⊂ decode k`. -/
def ssubE (j k nv : ℕ) : Expr := tAnd (subE j k nv) (tNot (subE k j nv))

/-- `tautological (decode k)`, by a loop over the variables. -/
def tautE (k nv : ℕ) : Expr :=
  tEx (.var nv)
    (tAnd (inE (.add (.mul (.lit 2) (.var 0)) (.lit 1)) (k + 1) (nv + 1))
      (inE (.add (.mul (.lit 2) (.var 0)) (.lit 2)) (k + 1) (nv + 1)))

/-- `(decode k).card`, by a loop over the literal codes. -/
def cardE (k nv : ℕ) : Expr := .sum (litsE nv) (inLE (k + 1) (nv + 1))

/-- The code in the variable `k` is valid. -/
def validE (k nv : ℕ) : Expr :=
  tAnd (tOr (tEq (d0E k nv) (.lit 0)) (tNot (tLe (d1E k nv) (d0E k nv))))
    (tOr (tEq (d1E k nv) (.lit 0)) (tNot (tLe (d2E k nv) (d1E k nv))))

/-- The word with bit `k` equal to the test `body`, for all codes `k`. -/
def setE (nv : ℕ) (body : Expr) : Expr := .sum (capE nv) (.mul (.pow2 (.var 0)) body)

section Tests

variable (hC : Ctx W n) (hn : env.getD nv 0 = n)
include hC hn

theorem run_d0 {k kv : ℕ} (hk : env.getD k 0 = kv) : Run W (d0E k nv) env (d0 n kv) 7 :=
  run_mod (run_var hk) (run_g hC hn)

theorem run_d1 {k kv : ℕ} (hk : env.getD k 0 = kv) : Run W (d1E k nv) env (d1 n kv) 13 :=
  run_mod (run_div (run_var hk) (run_g hC hn)) (run_g hC hn)

theorem run_d2 {k kv : ℕ} (hk : env.getD k 0 = kv) : Run W (d2E k nv) env (d2 n kv) 19 :=
  run_mod (run_div (run_div (run_var hk) (run_g hC hn)) (run_g hC hn)) (run_g hC hn)

theorem test_in {c : Expr} {v Bc k kv : ℕ} (hc : Run W c env v Bc) (hk : env.getD k 0 = kv) :
    Test W (inE c k nv) env (InC n v kv) (100 + 6 * Bc) := by
  have w := hC.one_le
  have h0 := test_eq w hc (run_d0 hC hn hk)
  have h1 := test_eq w hc (run_d1 hC hn hk)
  have h2 := test_eq w hc (run_d2 hC hn hk)
  have := test_or w h0 (fun _ => test_or w h1 (fun _ => h2))
  exact this.mono (by omega)

theorem test_validE {k kv : ℕ} (hk : env.getD k 0 = kv) :
    Test W (validE k nv) env (ValidC n kv) 150 := by
  have w := hC.one_le
  have a0 := run_d0 hC hn hk
  have a1 := run_d1 hC hn hk
  have a2 := run_d2 hC hn hk
  have z := run_zero (env := env) w
  have t1 := test_or w (test_eq w a0 z) (fun _ => test_not w (test_le w a1 a0))
  have t2 := test_or w (test_eq w a1 z) (fun _ => test_not w (test_le w a2 a1))
  have := test_and w t1 (fun _ => t2)
  refine (this.iff ?_).mono (by omega)
  simp only [ValidC, not_le]

end Tests

section Lits

variable (hC : Ctx W n) (hn : env.getD nv 0 = n)
include hC hn

theorem run_cE {c : ℕ} (hc : c < 2 * n) : Run W cE (c :: env) (c + 1) 3 :=
  run_add (run_var (gd0 c)) (run_one hC.one_le) (hC.le_lt (by omega))

theorem test_inL {k kv c : ℕ} (hc : c < 2 * n) (hk : (c :: env).getD k 0 = kv) :
    Test W (inLE k (nv + 1)) (c :: env) (InC n (c + 1) kv) 118 :=
  test_in hC (gd c hn) (run_cE hC hn hc) hk

theorem test_subE {j k jv kv : ℕ} (hj : env.getD j 0 = jv) (hk : env.getD k 0 = kv) :
    Test W (subE j k nv) env (decode n jv ⊆ decode n kv) (500 * (n + 1)) := by
  have w := hC.one_le
  have := test_all (p := fun c => ¬ InC n (c + 1) jv ∨ InC n (c + 1) kv) (B := 3 + (3 + 118) + 118) w
    (run_lits hC hn)
    (fun c hc => test_or w (test_not w (test_inL hC hn hc (gd c hj)))
      (fun _ => test_inL hC hn hc (gd c hk)))
  refine (this.iff ?_).mono (by omega)
  rw [decode_subset_iff]
  simp only [imp_iff_not_or]

theorem test_ssubE {j k jv kv : ℕ} (hj : env.getD j 0 = jv) (hk : env.getD k 0 = kv) :
    Test W (ssubE j k nv) env (decode n jv ⊂ decode n kv) (1010 * (n + 1)) := by
  have w := hC.one_le
  have := test_and w (test_subE hC hn hj hk) (fun _ => test_not w (test_subE hC hn hk hj))
  refine (this.iff ?_).mono (by omega)
  rw [Finset.ssubset_def]

theorem test_tautE {k kv : ℕ} (hk : env.getD k 0 = kv) :
    Test W (tautE k nv) env (tautological (decode n kv)) (300 * (n + 1)) := by
  have w := hC.one_le
  have h2 : (2 : ℕ) < 2 ^ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by
        have : 2 ^ 3 ≤ (2 * n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have := hC.big
        omega)
  have := test_ex (p := fun v => InC n (2 * v + 1) kv ∧ InC n (2 * v + 2) kv) (B := 3 + 130 + 130) w
    (run_var hn)
    (fun v hv => by
      have hd : Run W (.mul (.lit 2) (.var 0)) (v :: env) (2 * v) 3 :=
        run_mul (run_lit h2) (run_var (gd0 v)) (hC.le_lt (by omega))
      have h1 : Run W (.add (.mul (.lit 2) (.var 0)) (.lit 1)) (v :: env) (2 * v + 1) 5 :=
        run_add hd (run_one w) (hC.le_lt (by omega))
      have h3 : Run W (.add (.mul (.lit 2) (.var 0)) (.lit 2)) (v :: env) (2 * v + 2) 5 :=
        run_add hd (run_lit h2) (hC.le_lt (by omega))
      exact test_and w ((test_in hC (gd v hn) h1 (gd v hk)).mono (by omega))
        (fun _ => (test_in hC (gd v hn) h3 (gd v hk)).mono (by omega)))
  refine (this.iff tautological_decode.symm).mono (by omega)

theorem run_cardE {k kv : ℕ} (hk : env.getD k 0 = kv) :
    Run W (cardE k nv) env (decode n kv).card (240 * (n + 1)) := by
  have hle : ∑ c ∈ range (2 * n), ind (InC n (c + 1) kv) ≤ 3 := by
    rw [← card_decode]
    exact card_decode_le n kv
  have := run_sum (f := fun c => ind (InC n (c + 1) kv)) (run_lits hC hn)
    (fun c hc => test_inL hC hn hc (gd c hk))
    (hC.lt_pow (by have := hC.eight_le; omega))
  rw [← card_decode] at this
  exact this.mono (by omega)

theorem test_bit {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) {f k kv : ℕ}
    (hf : env.getD f 0 = encF n F) (hk : env.getD k 0 = kv) (hkv : kv < cap n) :
    Test W (bitE f k) env (Cl n F kv) 6 := by
  refine ⟨?_, (ops_bitE W f k env).le⟩
  rw [eval_bitE W f k env hC.two_le (by rw [hk]; exact hkv.trans hC.cap_lt), hf, hk]
  by_cases h : Cl n F kv
  · rw [ind_pos h, (encF_testBit hF hkv).mpr h]
    rfl
  · rw [ind_neg h]
    have : (encF n F).testBit kv ≠ true := fun h' => h ((encF_testBit hF hkv).mp h')
    simp only [Bool.not_eq_true] at this
    rw [this]
    rfl

theorem run_setE {body : Expr} {B : ℕ} {p : ℕ → Prop}
    (hb : ∀ k < cap n, Test W body (k :: env) (p k) B) :
    Run W (setE nv body) env (setWord (cap n) p) (18 + cap n * (B + 4)) := by
  have hw : 2 ^ cap n ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hC.cap_lt.le
  have := run_sum (f := fun k => 2 ^ k * ind (p k)) (B := B + 3) (run_cap hC hn)
    (fun k hk => by
      have hk' : k < W := hk.trans hC.cap_lt
      have h1 := run_pow2 (run_var (gd0 (env := env) k)) hk'
      have h2 : 2 ^ k * ind (p k) < 2 ^ W := by
        calc 2 ^ k * ind (p k) ≤ 2 ^ k * 1 := Nat.mul_le_mul_left _ (ind_le_one _)
          _ = 2 ^ k := mul_one _
          _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hk'
      exact (run_mul h1 (hb k hk) h2).mono (by omega))
    (lt_of_lt_of_le (setWord_lt (cap n) p) hw)
  have e : cap n * (B + 3 + 1) = cap n * (B + 4) := rfl
  exact this.mono (by omega)

end Lits

/-! ### Normalization -/

theorem Wide3.normalize {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) : Wide3 (normalizeClauses F) :=
  fun C hC => hF C (normalizeClauses_subset F hC)

theorem cl_normalize {F : ClauseSet (SignedLiteral n)} (hF : Wide3 F) (k : ℕ) :
    (Cl n F k ∧ ¬ tautological (decode n k) ∧
      ¬ ∃ j < cap n, Cl n F j ∧ ¬ tautological (decode n j) ∧ decode n j ⊂ decode n k) ↔
      Cl n (normalizeClauses F) k := by
  have e := exists_clause hF (fun D => ¬ tautological D ∧ D ⊂ decode n k)
  simp only [Cl, normalizeClauses, minimalClauses, mem_filter] at e ⊢
  rw [← e]
  simp only [not_exists, not_and, and_imp]
  tauto

/-- The word of `normalizeClauses F`, from the word of `F` in the variable `f`. -/
def normE (f nv : ℕ) : Expr :=
  setE nv
    (tAnd (bitE (f + 1) 0)
      (tAnd (tNot (tautE 0 (nv + 1)))
        (tNot (tEx (capE (nv + 1))
          (tAnd (bitE (f + 2) 0)
            (tAnd (tNot (tautE 0 (nv + 2))) (ssubE 0 1 (nv + 2))))))))

theorem run_normE (hC : Ctx W n) (hn : env.getD nv 0 = n) {F : ClauseSet (SignedLiteral n)}
    (hF : Wide3 F) {f : ℕ} (hf : env.getD f 0 = encF n F) :
    Run W (normE f nv) env (encF n (normalizeClauses F)) (93700 * (n + 1) ^ 7) := by
  have w := hC.one_le
  have m1 : (n + 1) ^ 1 ≤ (n + 1) ^ 4 := pow_le_pow_m n (by norm_num)
  have m1' : (n + 1) ^ 1 = n + 1 := pow_one _
  have m0 : 1 ≤ n + 1 := by omega
  have := run_setE (body := tAnd (bitE (f + 1) 0)
      (tAnd (tNot (tautE 0 (nv + 1)))
        (tNot (tEx (capE (nv + 1))
          (tAnd (bitE (f + 2) 0)
            (tAnd (tNot (tautE 0 (nv + 2))) (ssubE 0 1 (nv + 2))))))))
    (B := 11700 * (n + 1) ^ 4)
    (p := fun k => Cl n F k ∧ ¬ tautological (decode n k) ∧
      ¬ ∃ j < cap n, Cl n F j ∧ ¬ tautological (decode n j) ∧ decode n j ⊂ decode n k)
    hC hn (fun k hk => by
      have hn1 := gd k hn
      have hf1 := gd k hf
      have hinner := test_ex (N := cap n) (B := 1400 * (n + 1))
        (p := fun j => Cl n F j ∧ ¬ tautological (decode n j) ∧ decode n j ⊂ decode n k) w
        (run_cap hC hn1)
        (fun j hj => by
          have hn2 := gd j hn1
          have hf2 := gd j hf1
          have t1 := test_bit hC hn2 hF hf2 (gd0 j) hj
          have t2 := test_tautE hC hn2 (gd0 j)
          have t3 := test_ssubE hC hn2 (gd0 j) (gd j (gd0 k))
          have := test_and w t1 (fun _ => test_and w (test_not w t2) (fun _ => t3))
          exact this.mono (by omega))
      have hb : 4 + 17 + cap n * (1400 * (n + 1) + 4) ≤ 11300 * (n + 1) ^ (3 + 1) :=
        loop_le' (a := 8) (c := 1400) (d := 1) m0 (cap_le_pow n) (by omega) (by norm_num)
      have t1 := test_bit hC hn1 hF hf1 (gd0 k) hk
      have t2 := test_tautE hC hn1 (gd0 k)
      have := test_and w t1 (fun _ => test_and w (test_not w t2) (fun _ => test_not w hinner))
      refine this.mono ?_
      have : (3 + 1) = 4 := rfl
      simp only [this] at hb
      omega)
  have h2 : 18 + cap n * (11700 * (n + 1) ^ 4 + 4) ≤ 93700 * (n + 1) ^ (3 + 4) :=
    loop_le' (a := 8) (c := 11700) (d := 4) m0 (cap_le_pow n) le_rfl (by norm_num)
  refine (this.mono h2).val ?_
  exact setWord_eq_encF hF.normalize (fun k _ => cl_normalize hF k)

end TransposeBase.Pseudo.CnfTree
