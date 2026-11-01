import TransposeBase.Pseudo.Lang

/-!
# Small helpers on words

Exact values when nothing wraps around, and digits and bits of a word. Helpers take variable indices as
arguments, so an argument never has to be shifted under a binder.
-/

namespace TransposeBase.Pseudo

open Finset

variable (W : ℕ)

theorem foldl_sum_nat (f : ℕ → ℕ) (l : List ℕ) (s : ℕ) :
    l.foldl (fun st k => (st + f k) % 2 ^ W) (s % 2 ^ W) = (s + (l.map f).sum) % 2 ^ W := by
  induction l generalizing s with
  | nil => simp
  | cons k l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have h : (s % 2 ^ W + f k) % 2 ^ W = (s + f k) % 2 ^ W % 2 ^ W := by simp [Nat.add_mod]
    rw [h, ih, Nat.mod_add_mod, add_assoc]

theorem foldl_prod_nat (f : ℕ → ℕ) (l : List ℕ) (s : ℕ) :
    l.foldl (fun st k => (st * f k) % 2 ^ W) (s % 2 ^ W) = (s * (l.map f).prod) % 2 ^ W := by
  induction l generalizing s with
  | nil => simp
  | cons k l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    have h : (s % 2 ^ W * f k) % 2 ^ W = (s * f k) % 2 ^ W % 2 ^ W := by simp [Nat.mul_mod]
    rw [h, ih, Nat.mod_mul_mod, mul_assoc]

/-- A sum as a natural number. -/
theorem eval_sum (n b : Expr) (env : List ℕ) :
    eval W (.sum n b) env = (∑ k ∈ range (eval W n env), eval W b (k :: env)) % 2 ^ W := by
  simp only [eval]
  have := foldl_sum_nat W (fun k => eval W b (k :: env)) (List.range (eval W n env)) 0
  rw [Nat.zero_mod] at this
  rw [this, zero_add, ← List.toFinset_range, List.sum_toFinset _ List.nodup_range]

/-- A product as a natural number. -/
theorem eval_prod (n b : Expr) (env : List ℕ) :
    eval W (.prod n b) env = (∏ k ∈ range (eval W n env), eval W b (k :: env)) % 2 ^ W := by
  simp only [eval]
  rw [foldl_prod_nat, one_mul, ← List.toFinset_range, List.prod_toFinset _ List.nodup_range]

/-- `b ^ i`, for variables `b` and `i`. -/
def powE (b i : ℕ) : Expr := .prod (.var i) (.var (b + 1))

theorem eval_powE (b i : ℕ) (env : List ℕ) :
    eval W (powE b i) env = env.getD b 0 ^ env.getD i 0 % 2 ^ W := by
  simp [powE, eval_prod, eval]

theorem ops_powE (b i : ℕ) (env : List ℕ) : ops W (powE b i) env ≤ 2 + env.getD i 0 * 2 := by
  have := ops_prod_le W (.var i) (.var (b + 1)) env (B := 1) (fun k _ => by simp [ops])
  simp only [powE, ops, eval] at this ⊢
  omega

/-- Digit `i` of `k` in base `G`, for variables `k`, `G`, `i`. -/
def digE (k G i : ℕ) : Expr := .mod (.div (.var k) (powE G i)) (.var G)

theorem eval_digE (k G i : ℕ) (env : List ℕ) (h : env.getD G 0 ^ env.getD i 0 < 2 ^ W) :
    eval W (digE k G i) env = env.getD k 0 / env.getD G 0 ^ env.getD i 0 % env.getD G 0 := by
  simp only [digE, eval]
  rw [eval_powE, Nat.mod_eq_of_lt h]

theorem ops_digE (k G i : ℕ) (env : List ℕ) : ops W (digE k G i) env ≤ 6 + env.getD i 0 * 2 := by
  have := ops_powE W G i env
  simp only [digE, ops]
  omega

/-- Bit `i` of `k`, for variables `k`, `i`. -/
def bitE (k i : ℕ) : Expr := .mod (.div (.var k) (.pow2 (.var i))) (.lit 2)

theorem eval_bitE (k i : ℕ) (env : List ℕ) (hW : 2 ≤ W) (h : env.getD i 0 < W) :
    eval W (bitE k i) env = ((env.getD k 0).testBit (env.getD i 0)).toNat := by
  have h2 : 2 % 2 ^ W = 2 := Nat.mod_eq_of_lt (by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega))
  change (env.getD k 0 / (if env.getD i 0 < W then 2 ^ env.getD i 0 else 0)) % (2 % 2 ^ W) = _
  rw [if_pos h, h2, Nat.testBit_eq_decide_div_mod_eq]
  generalize env.getD k 0 / 2 ^ env.getD i 0 = z
  rcases Nat.mod_two_eq_zero_or_one z with hz | hz <;> simp [hz]

theorem ops_bitE (k i : ℕ) (env : List ℕ) : ops W (bitE k i) env = 6 := by
  simp [bitE, ops]

/-- `if x = y then c else d`, for variables `x`, `y`. -/
def eqE (x y : ℕ) (c d : Expr) : Expr := .ite (.var x) (.var y) (.ite (.var y) (.var x) c d) d

theorem eval_eqE (x y : ℕ) (c d : Expr) (env : List ℕ) :
    eval W (eqE x y c d) env = if env.getD x 0 = env.getD y 0 then eval W c env else eval W d env := by
  change (if env.getD x 0 ≤ env.getD y 0 then
    (if env.getD y 0 ≤ env.getD x 0 then eval W c env else eval W d env) else eval W d env) = _
  by_cases h : env.getD x 0 = env.getD y 0
  · rw [if_pos h, if_pos h.le, if_pos h.ge]
  · rw [if_neg h]
    by_cases h1 : env.getD x 0 ≤ env.getD y 0
    · rw [if_pos h1, if_neg (by omega)]
    · rw [if_neg h1]

theorem ops_eqE (x y : ℕ) (c d : Expr) (env : List ℕ) {B : ℕ} (hc : ops W c env ≤ B)
    (hd : ops W d env ≤ B) : ops W (eqE x y c d) env ≤ B + 6 := by
  simp only [eqE, ops]
  split_ifs <;> omega

end TransposeBase.Pseudo
