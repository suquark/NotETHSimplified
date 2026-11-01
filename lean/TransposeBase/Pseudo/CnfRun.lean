import TransposeBase.Pseudo.Words
import TransposeBase.Pseudo.CnfCode

/-!
# A small calculus for values and costs, and the clause tests

`Run W e env v B` says that `e` has the value `v` and costs at most `B` word operations. `Test W e env p B` is
the case where the value is the indicator of the proposition `p`. Each combinator below is one program in
`Expr` with its value and its cost, so that a theorem about a composite program is its own proof of cost.

The clause tests read the number `n` from a variable (`nv`), and clause codes from variables. They loop over
the `2 * n` literal codes where this is the simplest test. That costs a factor `n`, which is counted.
-/

namespace TransposeBase.Pseudo.CnfTree

open SatBase Finset

def Run (W : ℕ) (e : Expr) (env : List ℕ) (v B : ℕ) : Prop := eval W e env = v ∧ ops W e env ≤ B

abbrev Test (W : ℕ) (e : Expr) (env : List ℕ) (p : Prop) (B : ℕ) : Prop := Run W e env (ind p) B

variable {W : ℕ} {env : List ℕ}

theorem Run.mono {e : Expr} {v B B' : ℕ} (h : Run W e env v B) (hB : B ≤ B') : Run W e env v B' :=
  ⟨h.1, h.2.trans hB⟩

theorem Run.val {e : Expr} {v v' B : ℕ} (h : Run W e env v B) (hv : v = v') : Run W e env v' B :=
  hv ▸ h

theorem Test.iff {e : Expr} {p q : Prop} {B : ℕ} (h : Test W e env p B) (hpq : p ↔ q) :
    Test W e env q B := h.val (ind_congr hpq)

theorem gd (x : ℕ) {i v : ℕ} (h : env.getD i 0 = v) : (x :: env).getD (i + 1) 0 = v := by
  simpa using h

theorem gd0 (x : ℕ) : (x :: env).getD 0 0 = x := by simp

/-! ### Primitive steps -/

theorem run_var {i v : ℕ} (h : env.getD i 0 = v) : Run W (.var i) env v 1 := ⟨h, by simp [ops]⟩

theorem run_lit {m : ℕ} (h : m < 2 ^ W) : Run W (.lit m) env m 1 :=
  ⟨eval_lit_small W h, by simp [ops]⟩

theorem run_add {a b : Expr} {va vb Ba Bb : ℕ} (ha : Run W a env va Ba) (hb : Run W b env vb Bb)
    (h : va + vb < 2 ^ W) : Run W (.add a b) env (va + vb) (1 + Ba + Bb) := by
  refine ⟨by simp [eval, ha.1, hb.1, Nat.mod_eq_of_lt h], ?_⟩
  have := ha.2
  have := hb.2
  simp only [ops]
  omega

theorem run_mul {a b : Expr} {va vb Ba Bb : ℕ} (ha : Run W a env va Ba) (hb : Run W b env vb Bb)
    (h : va * vb < 2 ^ W) : Run W (.mul a b) env (va * vb) (1 + Ba + Bb) := by
  refine ⟨by simp [eval, ha.1, hb.1, Nat.mod_eq_of_lt h], ?_⟩
  have := ha.2
  have := hb.2
  simp only [ops]
  omega

theorem run_sub {a b : Expr} {va vb Ba Bb : ℕ} (ha : Run W a env va Ba) (hb : Run W b env vb Bb)
    (h : vb ≤ va) (h2 : va < 2 ^ W) : Run W (.sub a b) env (va - vb) (1 + Ba + Bb) := by
  constructor
  · simp only [eval, ha.1, hb.1]
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt h h2)]
    have : va + (2 ^ W - vb) = (va - vb) + 2 ^ W := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have := ha.2
    have := hb.2
    simp only [ops]
    omega

theorem run_div {a b : Expr} {va vb Ba Bb : ℕ} (ha : Run W a env va Ba) (hb : Run W b env vb Bb) :
    Run W (.div a b) env (va / vb) (1 + Ba + Bb) := by
  refine ⟨by simp [eval, ha.1, hb.1], ?_⟩
  have := ha.2
  have := hb.2
  simp only [ops]
  omega

theorem run_mod {a b : Expr} {va vb Ba Bb : ℕ} (ha : Run W a env va Ba) (hb : Run W b env vb Bb) :
    Run W (.mod a b) env (va % vb) (1 + Ba + Bb) := by
  refine ⟨by simp [eval, ha.1, hb.1], ?_⟩
  have := ha.2
  have := hb.2
  simp only [ops]
  omega

theorem run_pow2 {a : Expr} {va Ba : ℕ} (ha : Run W a env va Ba) (h : va < W) :
    Run W (.pow2 a) env (2 ^ va) (1 + Ba) := by
  refine ⟨by simp [eval, ha.1, h], ?_⟩
  have := ha.2
  simp only [ops]
  omega

theorem run_ite {a b c d : Expr} {va vb v Ba Bb Bc : ℕ} (ha : Run W a env va Ba) (hb : Run W b env vb Bb)
    (hc : va ≤ vb → Run W c env v Bc) (hd : ¬ va ≤ vb → Run W d env v Bc) :
    Run W (.ite a b c d) env v (1 + Ba + Bb + Bc) := by
  have h1 := ha.2
  have h2 := hb.2
  by_cases h : va ≤ vb
  · have h3 := hc h
    refine ⟨by simp only [eval, ha.1, hb.1, if_pos h, h3.1], ?_⟩
    have := h3.2
    simp only [ops, ha.1, hb.1, if_pos h]
    omega
  · have h3 := hd h
    refine ⟨by simp only [eval, ha.1, hb.1, if_neg h, h3.1], ?_⟩
    have := h3.2
    simp only [ops, ha.1, hb.1, if_neg h]
    omega

theorem run_let {a b : Expr} {va v Ba Bb : ℕ} (ha : Run W a env va Ba)
    (hb : Run W b (va :: env) v Bb) : Run W (.letE a b) env v (1 + Ba + Bb) := by
  refine ⟨by simp only [eval, ha.1, hb.1], ?_⟩
  have := ha.2
  have := hb.2
  simp only [ops, ha.1]
  omega

/-- A `fold`, given the trajectory `g` of its state. -/
theorem run_fold {n s b : Expr} {N Bn Bs B : ℕ} (g : ℕ → ℕ) (hn : Run W n env N Bn)
    (hs : Run W s env (g 0) Bs) (hb : ∀ k < N, Run W b (g k :: k :: env) (g (k + 1)) B) :
    Run W (.fold n s b) env (g N) (1 + Bn + Bs + N * (B + 1)) := by
  constructor
  · rw [eval_fold, hn.1, hs.1]
    have key : ∀ m ≤ N, (List.range m).foldl (fun st k => eval W b (st :: k :: env)) (g 0) = g m := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [ih (by omega)]
        exact (hb m (by omega)).1
    exact key N le_rfl
  · have := ops_fold_le W n s b env (fun k st => st = g k) (B := B) hs.1
      (fun k st hk hst => by
        rw [hn.1] at hk
        subst hst
        exact (hb k hk).1)
      (fun k st hk hst => by
        rw [hn.1] at hk
        subst hst
        exact (hb k hk).2)
    rw [hn.1] at this
    have := hn.2
    have := hs.2
    omega

theorem run_sum {n b : Expr} {N Bn B : ℕ} {f : ℕ → ℕ} (hn : Run W n env N Bn)
    (hb : ∀ k < N, Run W b (k :: env) (f k) B) (h : ∑ k ∈ range N, f k < 2 ^ W) :
    Run W (.sum n b) env (∑ k ∈ range N, f k) (1 + Bn + N * (B + 1)) := by
  constructor
  · rw [eval_sum, hn.1, sum_congr rfl (fun k hk => (hb k (mem_range.mp hk)).1), Nat.mod_eq_of_lt h]
  · have := ops_sum_le W n b env (B := B) (fun k hk => by rw [hn.1] at hk; exact (hb k hk).2)
    rw [hn.1] at this
    have := hn.2
    omega

/-! ### Tests -/

def tNot (a : Expr) : Expr := .ite a (.lit 0) (.lit 1) (.lit 0)
def tAnd (a b : Expr) : Expr := .ite a (.lit 0) (.lit 0) b
def tOr (a b : Expr) : Expr := .ite a (.lit 0) b (.lit 1)
def tLe (a b : Expr) : Expr := .ite a b (.lit 1) (.lit 0)
def tEq (a b : Expr) : Expr := .ite a b (.ite b a (.lit 1) (.lit 0)) (.lit 0)
def tAll (n b : Expr) : Expr := .prod n b
def tEx (n b : Expr) : Expr := tNot (tAll n (tNot b))

section Tests

variable (hW : 1 ≤ W)
include hW

theorem one_lt_pow : 1 < 2 ^ W := Nat.one_lt_two_pow (by omega)

theorem run_zero : Run W (.lit 0) env 0 1 := run_lit (by positivity)
theorem run_one : Run W (.lit 1) env 1 1 := run_lit (one_lt_pow hW)

theorem test_not {a : Expr} {p : Prop} {Ba : ℕ} (ha : Test W a env p Ba) :
    Test W (tNot a) env (¬p) (3 + Ba) := by
  have h := run_ite (c := .lit 1) (d := .lit 0) (v := ind (¬p)) (Bc := 1) ha (run_zero hW)
    (fun h => by
      have hp : ¬p := by rwa [Nat.le_zero, ind_eq_zero] at h
      rw [ind_pos hp]
      exact run_one hW)
    (fun h => by
      have hp : p := by
        rw [Nat.le_zero, ind_eq_zero, not_not] at h
        exact h
      rw [ind_neg (not_not.mpr hp)]
      exact run_zero hW)
  exact h.mono (by omega)

theorem test_and {a b : Expr} {p q : Prop} {Ba Bb : ℕ} (ha : Test W a env p Ba)
    (hb : p → Test W b env q Bb) : Test W (tAnd a b) env (p ∧ q) (3 + Ba + Bb) := by
  have h := run_ite (c := .lit 0) (d := b) (v := ind (p ∧ q)) (Bc := Bb + 1) ha (run_zero hW)
    (fun h => by
      have hp : ¬p := by rwa [Nat.le_zero, ind_eq_zero] at h
      rw [ind_neg (fun h' => hp h'.1)]
      exact (run_zero hW).mono (by omega))
    (fun h => by
      have hp : p := by
        rw [Nat.le_zero, ind_eq_zero, not_not] at h
        exact h
      exact ((hb hp).mono (by omega)).val (ind_congr (by simp [hp])))
  exact h.mono (by omega)

theorem test_or {a b : Expr} {p q : Prop} {Ba Bb : ℕ} (ha : Test W a env p Ba)
    (hb : ¬p → Test W b env q Bb) : Test W (tOr a b) env (p ∨ q) (3 + Ba + Bb) := by
  have h := run_ite (c := b) (d := .lit 1) (v := ind (p ∨ q)) (Bc := Bb + 1) ha (run_zero hW)
    (fun h => by
      have hp : ¬p := by rwa [Nat.le_zero, ind_eq_zero] at h
      exact ((hb hp).mono (by omega)).val (ind_congr (by simp [hp])))
    (fun h => by
      have hp : p := by
        rw [Nat.le_zero, ind_eq_zero, not_not] at h
        exact h
      rw [ind_pos (Or.inl hp)]
      exact (run_one hW).mono (by omega))
  exact h.mono (by omega)

theorem test_le {a b : Expr} {va vb Ba Bb : ℕ} (ha : Run W a env va Ba) (hb : Run W b env vb Bb) :
    Test W (tLe a b) env (va ≤ vb) (2 + Ba + Bb) := by
  have h := run_ite (c := .lit 1) (d := .lit 0) (v := ind (va ≤ vb)) (Bc := 1) ha hb
    (fun h => by rw [ind_pos h]; exact run_one hW)
    (fun h => by rw [ind_neg h]; exact run_zero hW)
  exact h.mono (by omega)

theorem test_eq {a b : Expr} {va vb Ba Bb : ℕ} (ha : Run W a env va Ba) (hb : Run W b env vb Bb) :
    Test W (tEq a b) env (va = vb) (3 + 2 * Ba + 2 * Bb) := by
  have h := run_ite (c := .ite b a (.lit 1) (.lit 0)) (d := .lit 0) (v := ind (va = vb))
    (Bc := 2 + Ba + Bb) ha hb
    (fun h => by
      have := test_le hW hb ha
      refine (this.mono (by omega)).val (ind_congr ?_)
      omega)
    (fun h => by
      rw [ind_neg (by omega)]
      exact (run_zero hW).mono (by omega))
  exact h.mono (by omega)

theorem prod_ind {N : ℕ} (p : ℕ → Prop) : ∏ k ∈ range N, ind (p k) = ind (∀ k < N, p k) := by
  by_cases h : ∀ k < N, p k
  · rw [ind_pos h]
    exact prod_eq_one (fun k hk => ind_pos (h k (mem_range.mp hk)))
  · rw [ind_neg h]
    push Not at h
    obtain ⟨k, hk, hp⟩ := h
    exact prod_eq_zero (mem_range.mpr hk) (ind_neg hp)

theorem test_all {n b : Expr} {N Bn B : ℕ} {p : ℕ → Prop} (hn : Run W n env N Bn)
    (hb : ∀ k < N, Test W b (k :: env) (p k) B) :
    Test W (tAll n b) env (∀ k < N, p k) (1 + Bn + N * (B + 1)) := by
  constructor
  · simp only [tAll]
    rw [eval_prod, hn.1, prod_congr rfl (fun k hk => (hb k (mem_range.mp hk)).1), prod_ind hW]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (ind_le_one _) (one_lt_pow hW))
  · have := ops_prod_le W n b env (B := B) (fun k hk => by rw [hn.1] at hk; exact (hb k hk).2)
    rw [hn.1] at this
    have := hn.2
    simp only [tAll]
    omega

theorem test_ex {n b : Expr} {N Bn B : ℕ} {p : ℕ → Prop} (hn : Run W n env N Bn)
    (hb : ∀ k < N, Test W b (k :: env) (p k) B) :
    Test W (tEx n b) env (∃ k < N, p k) (4 + Bn + N * (B + 4)) := by
  have h := test_not hW (test_all (p := fun k => ¬ p k) (B := 3 + B) hW hn
    (fun k hk => test_not hW (hb k hk)))
  have e : (¬ ∀ k < N, ¬ p k) ↔ ∃ k < N, p k := by push Not; rfl
  refine (h.iff e).mono ?_
  have : N * (3 + B + 1) = N * (B + 4) := by ring_nf
  omega

end Tests

/-! ### The size condition -/

/-- The word is long enough for every code. -/
structure Ctx (W n : ℕ) : Prop where
  big : (2 * n + 2) ^ 3 ≤ W

namespace Ctx

variable {n : ℕ}

theorem cap_lt (h : Ctx W n) : cap n < W :=
  lt_of_lt_of_le (Nat.pow_lt_pow_left (by omega) (by norm_num)) h.big

theorem one_le (h : Ctx W n) : 1 ≤ W := by have := h.cap_lt; omega

theorem G_le_cap (n : ℕ) : 2 * n + 1 ≤ cap n := Nat.le_self_pow (by norm_num) _

theorem two_le (h : Ctx W n) : 2 ≤ W := by
  have h1 : 2 ^ 3 ≤ (2 * n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have := h.big
  omega

theorem eight_le (h : Ctx W n) : 8 ≤ W := by
  have h1 : 2 ^ 3 ≤ (2 * n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have := h.big
  omega

theorem lt_pow (_h : Ctx W n) {x : ℕ} (hx : x < W) : x < 2 ^ W := hx.trans Nat.lt_two_pow_self

theorem G_lt (h : Ctx W n) : 2 * n + 1 < 2 ^ W :=
  h.lt_pow (lt_of_le_of_lt (G_le_cap n) h.cap_lt)

theorem le_lt (h : Ctx W n) {x : ℕ} (hx : x ≤ 2 * n + 1) : x < 2 ^ W := lt_of_le_of_lt hx h.G_lt

theorem cap_pow_lt (h : Ctx W n) {x : ℕ} (hx : x ≤ cap n) : x < 2 ^ W :=
  h.lt_pow (lt_of_le_of_lt hx h.cap_lt)

end Ctx

/-! ### Cost shapes -/

theorem loop_le' {K N a p c d m C B e : ℕ} (hm : 1 ≤ m) (hN : N ≤ a * m ^ p) (hB : B ≤ c * m ^ d)
    (hC : K + a * (c + e) ≤ C) : K + N * (B + e) ≤ C * m ^ (p + d) := by
  have h1 : 1 ≤ m ^ (p + d) := Nat.one_le_pow _ _ hm
  have h2 : 1 ≤ m ^ d := Nat.one_le_pow _ _ hm
  have h3 : B + e ≤ (c + e) * m ^ d := by nlinarith
  have h4 : N * (B + e) ≤ a * (c + e) * m ^ (p + d) := by
    calc N * (B + e) ≤ (a * m ^ p) * ((c + e) * m ^ d) := Nat.mul_le_mul hN h3
      _ = a * (c + e) * m ^ (p + d) := by rw [pow_add]; ring
  have h5 : K ≤ K * m ^ (p + d) := Nat.le_mul_of_pos_right _ (by omega)
  calc K + N * (B + e) ≤ (K + a * (c + e)) * m ^ (p + d) := by nlinarith
    _ ≤ C * m ^ (p + d) := Nat.mul_le_mul_right _ hC

theorem pow_le_pow_m (n : ℕ) {a b : ℕ} (h : a ≤ b) : (n + 1) ^ a ≤ (n + 1) ^ b :=
  Nat.pow_le_pow_right (by omega) h

theorem cap_le_pow (n : ℕ) : cap n ≤ 8 * (n + 1) ^ 3 := by
  calc (2 * n + 1) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    _ = 8 * (n + 1) ^ 3 := by ring

section Digits

variable {n nv : ℕ}

def gE (nv : ℕ) : Expr := .add (.mul (.lit 2) (.var nv)) (.lit 1)
def litsE (nv : ℕ) : Expr := .mul (.lit 2) (.var nv)
def capE (nv : ℕ) : Expr := .mul (.mul (gE nv) (gE nv)) (gE nv)

variable (hC : Ctx W n) (hn : env.getD nv 0 = n)
include hC hn

theorem run_lits : Run W (litsE nv) env (2 * n) 3 := by
  have h3 : (2 : ℕ) < 2 ^ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by
        have : 2 ^ 3 ≤ (2 * n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have := hC.big
        omega)
  exact (run_mul (run_lit h3) (run_var hn) (hC.le_lt (by omega))).mono (by omega)

theorem run_g : Run W (gE nv) env (2 * n + 1) 5 := by
  have := run_add (run_lits hC hn) (run_one hC.one_le) (hC.le_lt le_rfl)
  exact this

theorem run_cap : Run W (capE nv) env (cap n) 17 := by
  have g := run_g hC hn
  have h1 : (2 * n + 1) * (2 * n + 1) ≤ cap n := by
    show (2 * n + 1) * (2 * n + 1) ≤ (2 * n + 1) ^ 3
    nlinarith [sq_nonneg (2 * n + 1), Nat.le_self_pow (n := 2) (by norm_num) (2 * n + 1),
      Nat.pos_of_ne_zero (show (2 * n + 1) * (2 * n + 1) ≠ 0 by positivity)]
  have h2 := run_mul g g (hC.cap_pow_lt h1)
  have h3 := run_mul h2 g (hC.cap_pow_lt (x := (2 * n + 1) * (2 * n + 1) * (2 * n + 1)) (le_of_eq (by ring)))
  exact (h3.val (by ring)).mono (by omega)

end Digits

end TransposeBase.Pseudo.CnfTree
