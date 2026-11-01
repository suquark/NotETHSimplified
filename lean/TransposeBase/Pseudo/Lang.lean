import Mathlib

/-!
# A word language for the pseudocode layer

Programs are expressions over `W`-bit words. There is one data type, the natural number below `2 ^ W`,
and bounded loops are the only form of repetition, so every program terminates.

* `eval W e env`: the value. Addition, subtraction and multiplication are taken modulo `2 ^ W`.
* `ops W e env`: the number of word operations of the evaluation. Each constructor costs one, and a loop
  costs the sum over its actual iterations.
* `stack e`: the number of words that are live at the same time, besides the environment. It is static.

A word operation is an operation on `W` bits, so one operation costs a polynomial in `W` bit operations.
Reading a table is one operation on a word that holds the whole table, so a table costs its size in `W`.
No operation is free, and a loop bound is a value that the program computes.
-/

namespace TransposeBase.Pseudo

/-- Expressions. Variables are de Bruijn indices into the environment. -/
inductive Expr where
  | var (i : ℕ)
  | lit (n : ℕ)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | mod (a b : Expr)
  | pow2 (a : Expr)
  /-- `ite a b c d`: if `a ≤ b` then `c` else `d`. -/
  | ite (a b c d : Expr)
  /-- `letE a b`: evaluate `b` with the value of `a` as variable `0`. -/
  | letE (a b : Expr)
  /-- `fold n s b`: start with the state `s`. For `k < n`, replace the state by `b`, evaluated with the
  state as variable `0` and `k` as variable `1`. -/
  | fold (n s b : Expr)
  /-- `sum n b`: the sum modulo `2 ^ W` of `b` for `k < n`, with `k` as variable `0`. -/
  | sum (n b : Expr)
  /-- `prod n b`: the product modulo `2 ^ W` of `b` for `k < n`, with `k` as variable `0`. -/
  | prod (n b : Expr)
  /-- `sumIter n s f b`: the sum modulo `2 ^ W` of `b` over `n` iterates. The first iterate is `s`, and the
  next iterate is `f`, each with the current iterate as variable `0`. -/
  | sumIter (n s f b : Expr)
  deriving Inhabited

variable (W : ℕ)

/-- The value of an expression. -/
def eval : Expr → List ℕ → ℕ
  | .var i, env => env.getD i 0
  | .lit n, _ => n % 2 ^ W
  | .add a b, env => (eval a env + eval b env) % 2 ^ W
  | .sub a b, env => (eval a env + (2 ^ W - eval b env % 2 ^ W)) % 2 ^ W
  | .mul a b, env => (eval a env * eval b env) % 2 ^ W
  | .div a b, env => eval a env / eval b env
  | .mod a b, env => eval a env % eval b env
  | .pow2 a, env => if eval a env < W then 2 ^ eval a env else 0
  | .ite a b c d, env => if eval a env ≤ eval b env then eval c env else eval d env
  | .letE a b, env => eval b (eval a env :: env)
  | .fold n s b, env =>
      (List.range (eval n env)).foldl (fun st k => eval b (st :: k :: env)) (eval s env)
  | .sum n b, env =>
      (List.range (eval n env)).foldl (fun st k => (st + eval b (k :: env)) % 2 ^ W) 0
  | .prod n b, env =>
      (List.range (eval n env)).foldl (fun st k => (st * eval b (k :: env)) % 2 ^ W) (1 % 2 ^ W)
  | .sumIter n s f b, env =>
      ((List.range (eval n env)).foldl
        (fun p _ => (eval f (p.1 :: env), (p.2 + eval b (p.1 :: env)) % 2 ^ W))
        (eval s env, 0)).2

/-- The number of word operations. -/
def ops : Expr → List ℕ → ℕ
  | .var _, _ => 1
  | .lit _, _ => 1
  | .add a b, env => 1 + ops a env + ops b env
  | .sub a b, env => 1 + ops a env + ops b env
  | .mul a b, env => 1 + ops a env + ops b env
  | .div a b, env => 1 + ops a env + ops b env
  | .mod a b, env => 1 + ops a env + ops b env
  | .pow2 a, env => 1 + ops a env
  | .ite a b c d, env =>
      1 + ops a env + ops b env +
        if eval W a env ≤ eval W b env then ops c env else ops d env
  | .letE a b, env => 1 + ops a env + ops b (eval W a env :: env)
  | .fold n s b, env =>
      ((List.range (eval W n env)).foldl
        (fun p k => (eval W b (p.1 :: k :: env), p.2 + 1 + ops b (p.1 :: k :: env)))
        (eval W s env, 1 + ops n env + ops s env)).2
  | .sum n b, env =>
      1 + ops n env + ((List.range (eval W n env)).map fun k => 1 + ops b (k :: env)).sum
  | .prod n b, env =>
      1 + ops n env + ((List.range (eval W n env)).map fun k => 1 + ops b (k :: env)).sum
  | .sumIter n s f b, env =>
      ((List.range (eval W n env)).foldl
        (fun p _ => (eval W f (p.1 :: env), p.2 + 1 + ops b (p.1 :: env) + ops f (p.1 :: env)))
        (eval W s env, 1 + ops n env + ops s env)).2

/-- The number of words live at the same time, besides the environment. -/
def stack : Expr → ℕ
  | .var _ => 1
  | .lit _ => 1
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b => max (stack a) (1 + stack b)
  | .pow2 a => stack a
  | .ite a b c d => max (stack a) (max (1 + stack b) (max (stack c) (stack d)))
  | .letE a b => max (stack a) (1 + stack b)
  | .fold n s b => max (stack n) (max (1 + stack s) (3 + stack b))
  | .sum n b | .prod n b => max (stack n) (3 + stack b)
  | .sumIter n s f b => max (stack n) (max (1 + stack s) (4 + max (stack f) (stack b)))

/-! ### Loops -/

theorem fold_ops_aux (b : Expr) (env : List ℕ) (l : List ℕ) (s c : ℕ) :
    (l.foldl (fun p k => (eval W b (p.1 :: k :: env), p.2 + 1 + ops W b (p.1 :: k :: env))) (s, c)) =
      (l.foldl (fun st k => eval W b (st :: k :: env)) s,
        (l.foldl (fun p k => (eval W b (p.1 :: k :: env), p.2 + 1 + ops W b (p.1 :: k :: env)))
          (s, c)).2) := by
  induction l generalizing s c with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    rw [ih]

/-- A uniform bound on the body bounds the operations of a loop. The invariant `I` holds for the states
that the loop reaches. -/
theorem ops_fold_le (n s b : Expr) (env : List ℕ) (I : ℕ → ℕ → Prop) {B : ℕ}
    (h0 : I 0 (eval W s env))
    (hstep : ∀ k st, k < eval W n env → I k st → I (k + 1) (eval W b (st :: k :: env)))
    (hB : ∀ k st, k < eval W n env → I k st → ops W b (st :: k :: env) ≤ B) :
    ops W (.fold n s b) env ≤ 1 + ops W n env + ops W s env + eval W n env * (B + 1) := by
  have key : ∀ (m : ℕ), m ≤ eval W n env →
      I m ((List.range m).foldl (fun st k => eval W b (st :: k :: env)) (eval W s env)) ∧
      ((List.range m).foldl
        (fun p k => (eval W b (p.1 :: k :: env), p.2 + 1 + ops W b (p.1 :: k :: env)))
        (eval W s env, 1 + ops W n env + ops W s env)).2 ≤
        1 + ops W n env + ops W s env + m * (B + 1) := by
    intro m
    induction m with
    | zero => intro _; simpa using h0
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [fold_ops_aux]
      simp only
      refine ⟨hstep m _ (by omega) h1, ?_⟩
      have h3 := hB m _ (by omega) h1
      rw [fold_ops_aux] at h2
      simp only at h2
      nlinarith
  simpa [ops] using (key _ le_rfl).2

/-- The loop as a left fold. -/
theorem eval_fold (n s b : Expr) (env : List ℕ) :
    eval W (.fold n s b) env =
      (List.range (eval W n env)).foldl (fun st k => eval W b (st :: k :: env)) (eval W s env) := by
  simp [eval]

/-! ### Values in the ring of words -/

/-- The value of an expression in `ZMod (2 ^ W)`. -/
abbrev evalZ (e : Expr) (env : List ℕ) : ZMod (2 ^ W) := (eval W e env : ZMod (2 ^ W))

@[simp] theorem evalZ_add (a b : Expr) (env : List ℕ) :
    evalZ W (.add a b) env = evalZ W a env + evalZ W b env := by
  simp [evalZ, eval]

@[simp] theorem evalZ_mul (a b : Expr) (env : List ℕ) :
    evalZ W (.mul a b) env = evalZ W a env * evalZ W b env := by
  simp [evalZ, eval]

@[simp] theorem evalZ_lit (n : ℕ) (env : List ℕ) : evalZ W (.lit n) env = (n : ZMod (2 ^ W)) := by
  simp [evalZ, eval]

@[simp] theorem evalZ_sub (a b : Expr) (env : List ℕ) :
    evalZ W (.sub a b) env = evalZ W a env - evalZ W b env := by
  have h : ((eval W b env % 2 ^ W : ℕ) : ZMod (2 ^ W)) = (eval W b env : ZMod (2 ^ W)) := by simp
  have hle : eval W b env % 2 ^ W ≤ 2 ^ W := (Nat.mod_lt _ (by positivity)).le
  simp only [evalZ, eval, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, h]
  have h2 : (((2 : ℕ) : ZMod (2 ^ W)) ^ W) = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ W)
  rw [h2]
  ring

private theorem foldl_sum_cast (f : ℕ → ℕ) (l : List ℕ) (s : ℕ) :
    ((l.foldl (fun st k => (st + f k) % 2 ^ W) s : ℕ) : ZMod (2 ^ W)) =
      (s : ZMod (2 ^ W)) + (l.map fun k => (f k : ZMod (2 ^ W))).sum := by
  induction l generalizing s with
  | nil => simp
  | cons k l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    simp [add_assoc]

private theorem foldl_prod_cast (f : ℕ → ℕ) (l : List ℕ) (s : ℕ) :
    ((l.foldl (fun st k => (st * f k) % 2 ^ W) s : ℕ) : ZMod (2 ^ W)) =
      (s : ZMod (2 ^ W)) * (l.map fun k => (f k : ZMod (2 ^ W))).prod := by
  induction l generalizing s with
  | nil => simp
  | cons k l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih]
    simp [mul_assoc]

@[simp] theorem evalZ_sum (n b : Expr) (env : List ℕ) :
    evalZ W (.sum n b) env = ∑ k ∈ Finset.range (eval W n env), evalZ W b (k :: env) := by
  simp only [evalZ, eval]
  rw [foldl_sum_cast]
  rw [← List.toFinset_range, List.sum_toFinset _ List.nodup_range]
  simp

@[simp] theorem evalZ_prod (n b : Expr) (env : List ℕ) :
    evalZ W (.prod n b) env = ∏ k ∈ Finset.range (eval W n env), evalZ W b (k :: env) := by
  simp only [evalZ, eval]
  rw [foldl_prod_cast]
  rw [← List.toFinset_range, List.prod_toFinset _ List.nodup_range]
  simp

/-! ### Operations of `sum` and `prod` -/

/-- The `k`-th iterate of `sumIter`. -/
def iterate (f : Expr) (s : ℕ) (env : List ℕ) : ℕ → ℕ
  | 0 => s
  | k + 1 => eval W f (iterate f s env k :: env)

theorem foldl_iter_fst (f b : Expr) (env : List ℕ) (m : ℕ) (a c : ℕ) :
    ((List.range m).foldl (fun p _ => (eval W f (p.1 :: env), (p.2 + eval W b (p.1 :: env)) % 2 ^ W))
        (a, c)).1 = iterate W f a env m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    rfl

@[simp] theorem evalZ_sumIter (n s f b : Expr) (env : List ℕ) :
    evalZ W (.sumIter n s f b) env =
      ∑ k ∈ Finset.range (eval W n env),
        evalZ W b (iterate W f (eval W s env) env k :: env) := by
  simp only [evalZ, eval]
  generalize eval W n env = m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [foldl_iter_fst]
    simp only [ZMod.natCast_mod, Nat.cast_add]
    rw [ih]

theorem list_sum_map_range_le (f : ℕ → ℕ) (n B : ℕ) (h : ∀ k < n, f k ≤ B) :
    ((List.range n).map f).sum ≤ n * B := by
  have := List.sum_le_card_nsmul ((List.range n).map f) B (by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact h k (List.mem_range.mp hk))
  simpa using this

theorem ops_sum_le (n b : Expr) (env : List ℕ) {B : ℕ}
    (h : ∀ k < eval W n env, ops W b (k :: env) ≤ B) :
    ops W (.sum n b) env ≤ 1 + ops W n env + eval W n env * (B + 1) := by
  simp only [ops]
  have := list_sum_map_range_le (fun k => 1 + ops W b (k :: env)) (eval W n env) (B + 1)
    (fun k hk => by have := h k hk; show 1 + ops W b (k :: env) ≤ B + 1; omega)
  omega

theorem ops_prod_le (n b : Expr) (env : List ℕ) {B : ℕ}
    (h : ∀ k < eval W n env, ops W b (k :: env) ≤ B) :
    ops W (.prod n b) env ≤ 1 + ops W n env + eval W n env * (B + 1) := by
  simp only [ops]
  have := list_sum_map_range_le (fun k => 1 + ops W b (k :: env)) (eval W n env) (B + 1)
    (fun k hk => by have := h k hk; show 1 + ops W b (k :: env) ≤ B + 1; omega)
  omega

theorem ops_sumIter_le (n s f b : Expr) (env : List ℕ) {B : ℕ}
    (h : ∀ k < eval W n env,
      ops W b (iterate W f (eval W s env) env k :: env) +
        ops W f (iterate W f (eval W s env) env k :: env) ≤ B) :
    ops W (.sumIter n s f b) env ≤ 1 + ops W n env + ops W s env + eval W n env * (B + 1) := by
  have key : ∀ m, m ≤ eval W n env →
      ((List.range m).foldl
        (fun p _ => (eval W f (p.1 :: env), p.2 + 1 + ops W b (p.1 :: env) + ops W f (p.1 :: env)))
        (eval W s env, 1 + ops W n env + ops W s env)).1 = iterate W f (eval W s env) env m ∧
      ((List.range m).foldl
        (fun p _ => (eval W f (p.1 :: env), p.2 + 1 + ops W b (p.1 :: env) + ops W f (p.1 :: env)))
        (eval W s env, 1 + ops W n env + ops W s env)).2 ≤
        1 + ops W n env + ops W s env + m * (B + 1) := by
    intro m
    induction m with
    | zero => intro _; simp [iterate]
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [h1]
      refine ⟨rfl, ?_⟩
      have h3 := h m (by omega)
      nlinarith
  simpa [ops] using (key _ le_rfl).2

/-! ### Exact values when nothing wraps around -/

theorem eval_lit_small {n : ℕ} {env : List ℕ} (h : n < 2 ^ W) : eval W (.lit n) env = n := by
  simp [eval, Nat.mod_eq_of_lt h]

end TransposeBase.Pseudo
