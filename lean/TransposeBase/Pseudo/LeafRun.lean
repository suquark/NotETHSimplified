import TransposeBase.Pseudo.Words
import TransposeBase.Pseudo.Code

/-!
# Judgements for running a program

`Run W e env n c` says that `e` has the exact value `n` and costs at most `c` word operations.
`RunZ W e env z c` says that the value of `e` in the ring of words is the integer `z`, with the same cost.
Each constructor of `Expr` has a rule, so the value and the cost of a helper are proved together.

`liftE` is the de Bruijn shift: it runs a program of an outer environment under more binders.
-/

namespace TransposeBase.Pseudo.Leaf

open Finset

/-- The exact value of `e` is `n`, with at most `c` operations. -/
def Run (W : ℕ) (e : Expr) (env : List ℕ) (n c : ℕ) : Prop := eval W e env = n ∧ ops W e env ≤ c

/-- The value of `e` in the ring of words is the cast of the integer `z`, with at most `c` operations. -/
def RunZ (W : ℕ) (e : Expr) (env : List ℕ) (z : ℤ) (c : ℕ) : Prop :=
  evalZ W e env = (z : ZMod (2 ^ W)) ∧ ops W e env ≤ c

variable {W : ℕ} {env : List ℕ} {a b c d n s f : Expr} {x y z r k : ℕ} {ca cb cc cd cn B T : ℕ}
  {u v : ℤ}

/-! ### General rules -/

theorem Run.mono (h : Run W a env x ca) (hc : ca ≤ cb) : Run W a env x cb := ⟨h.1, h.2.trans hc⟩

theorem RunZ.mono (h : RunZ W a env u ca) (hc : ca ≤ cb) : RunZ W a env u cb := ⟨h.1, h.2.trans hc⟩

theorem Run.eq (h : Run W a env x ca) (hx : x = y) : Run W a env y ca := hx ▸ h

theorem RunZ.eq (h : RunZ W a env u ca) (hu : u = v) : RunZ W a env v ca := hu ▸ h

theorem Run.toZ (h : Run W a env x ca) : RunZ W a env (x : ℤ) ca :=
  ⟨by simp [evalZ, h.1], h.2⟩

theorem Run.var {i : ℕ} (h : env.getD i 0 = x) : Run W (.var i) env x 1 := ⟨h, le_rfl⟩

theorem Run.lit (h : x < 2 ^ W) : Run W (.lit x) env x 1 := ⟨eval_lit_small W h, le_rfl⟩

theorem RunZ.lit (x : ℕ) : RunZ W (.lit x) env (x : ℤ) 1 := ⟨by simp, le_rfl⟩

theorem RunZ.lit0 : RunZ W (.lit 0) env 0 1 := (RunZ.lit 0).eq (by simp)

theorem RunZ.lit1 : RunZ W (.lit 1) env 1 1 := (RunZ.lit 1).eq (by simp)

theorem Run.add (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x + y < 2 ^ W) :
    Run W (.add a b) env (x + y) (1 + ca + cb) := by
  refine ⟨?_, ?_⟩
  · simp only [eval, ha.1, hb.1, Nat.mod_eq_of_lt h]
  · have := ha.2; have := hb.2; simp only [ops]; omega

theorem Run.mul (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x * y < 2 ^ W) :
    Run W (.mul a b) env (x * y) (1 + ca + cb) := by
  refine ⟨?_, ?_⟩
  · simp only [eval, ha.1, hb.1, Nat.mod_eq_of_lt h]
  · have := ha.2; have := hb.2; simp only [ops]; omega

theorem Run.sub (ha : Run W a env x ca) (hb : Run W b env y cb) (h : x < 2 ^ W) (hy : y ≤ x) :
    Run W (.sub a b) env (x - y) (1 + ca + cb) := by
  refine ⟨?_, ?_⟩
  · simp only [eval, ha.1, hb.1]
    have hy' : y < 2 ^ W := by omega
    rw [Nat.mod_eq_of_lt hy']
    have : x + (2 ^ W - y) = (x - y) + 2 ^ W := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · have := ha.2; have := hb.2; simp only [ops]; omega

theorem Run.div (ha : Run W a env x ca) (hb : Run W b env y cb) :
    Run W (.div a b) env (x / y) (1 + ca + cb) := by
  refine ⟨by simp only [eval, ha.1, hb.1], ?_⟩
  have := ha.2; have := hb.2; simp only [ops]; omega

theorem Run.mod (ha : Run W a env x ca) (hb : Run W b env y cb) :
    Run W (.mod a b) env (x % y) (1 + ca + cb) := by
  refine ⟨by simp only [eval, ha.1, hb.1], ?_⟩
  have := ha.2; have := hb.2; simp only [ops]; omega

theorem Run.pow2 (ha : Run W a env x ca) (h : x < W) : Run W (.pow2 a) env (2 ^ x) (1 + ca) := by
  refine ⟨by simp only [eval, ha.1, if_pos h], ?_⟩
  have := ha.2; simp only [ops]; omega

theorem Run.ite (ha : Run W a env x ca) (hb : Run W b env y cb)
    (h1 : x ≤ y → Run W c env r cc) (h2 : ¬ x ≤ y → Run W d env r cd) :
    Run W (.ite a b c d) env r (1 + ca + cb + (cc + cd)) := by
  have := ha.2; have := hb.2
  by_cases h : x ≤ y
  · have h3 := h1 h
    refine ⟨by simp only [eval, ha.1, hb.1, if_pos h, h3.1], ?_⟩
    have := h3.2; simp only [ops, ha.1, hb.1, if_pos h]; omega
  · have h3 := h2 h
    refine ⟨by simp only [eval, ha.1, hb.1, if_neg h, h3.1], ?_⟩
    have := h3.2; simp only [ops, ha.1, hb.1, if_neg h]; omega

theorem RunZ.ite (ha : Run W a env x ca) (hb : Run W b env y cb)
    (h1 : x ≤ y → RunZ W c env u cc) (h2 : ¬ x ≤ y → RunZ W d env u cd) :
    RunZ W (.ite a b c d) env u (1 + ca + cb + (cc + cd)) := by
  have := ha.2; have := hb.2
  by_cases h : x ≤ y
  · have h3 := h1 h
    refine ⟨?_, ?_⟩
    · have : eval W (.ite a b c d) env = eval W c env := by simp only [eval, ha.1, hb.1, if_pos h]
      simp only [evalZ, this]; exact h3.1
    · have := h3.2; simp only [ops, ha.1, hb.1, if_pos h]; omega
  · have h3 := h2 h
    refine ⟨?_, ?_⟩
    · have : eval W (.ite a b c d) env = eval W d env := by simp only [eval, ha.1, hb.1, if_neg h]
      simp only [evalZ, this]; exact h3.1
    · have := h3.2; simp only [ops, ha.1, hb.1, if_neg h]; omega

/-- `if a = b then c else d`, for expressions `a`, `b`. -/
def eqX (a b c d : Expr) : Expr := .ite a b (.ite b a c d) d

theorem Run.eqX (ha : Run W a env x ca) (hb : Run W b env y cb)
    (h1 : x = y → Run W c env r cc) (h2 : x ≠ y → Run W d env r cd) :
    Run W (eqX a b c d) env r (2 + 2 * (ca + cb) + 2 * (cc + cd)) := by
  have h := Run.ite ha hb
    (c := .ite b a c d) (d := d) (r := r) (cc := 1 + cb + ca + (cc + cd)) (cd := cd)
    (fun hxy => Run.ite hb ha (fun hyx => h1 (by omega)) (fun hyx => h2 (by omega)))
    (fun hxy => h2 (by omega))
  exact h.mono (by omega)

theorem RunZ.eqX (ha : Run W a env x ca) (hb : Run W b env y cb)
    (h1 : x = y → RunZ W c env u cc) (h2 : x ≠ y → RunZ W d env u cd) :
    RunZ W (eqX a b c d) env u (2 + 2 * (ca + cb) + 2 * (cc + cd)) := by
  have h := RunZ.ite ha hb
    (c := .ite b a c d) (d := d) (u := u) (cc := 1 + cb + ca + (cc + cd)) (cd := cd)
    (fun hxy => RunZ.ite hb ha (fun hyx => h1 (by omega)) (fun hyx => h2 (by omega)))
    (fun hxy => h2 (by omega))
  exact h.mono (by omega)

theorem Run.letE (ha : Run W a env x ca) (hb : Run W b (x :: env) y cb) :
    Run W (.letE a b) env y (1 + ca + cb) := by
  refine ⟨by simp only [eval, ha.1, hb.1], ?_⟩
  have := ha.2; have := hb.2; simp only [ops, ha.1]; omega

theorem RunZ.letE (ha : Run W a env x ca) (hb : RunZ W b (x :: env) u cb) :
    RunZ W (.letE a b) env u (1 + ca + cb) := by
  refine ⟨?_, ?_⟩
  · have : eval W (.letE a b) env = eval W b (x :: env) := by simp only [eval, ha.1]
    simp only [evalZ, this]; exact hb.1
  · have := ha.2; have := hb.2; simp only [ops, ha.1]; omega

theorem RunZ.add (ha : RunZ W a env u ca) (hb : RunZ W b env v cb) :
    RunZ W (.add a b) env (u + v) (1 + ca + cb) := by
  refine ⟨by rw [evalZ_add, ha.1, hb.1]; push_cast; rfl, ?_⟩
  have := ha.2; have := hb.2; simp only [ops]; omega

theorem RunZ.sub (ha : RunZ W a env u ca) (hb : RunZ W b env v cb) :
    RunZ W (.sub a b) env (u - v) (1 + ca + cb) := by
  refine ⟨by rw [evalZ_sub, ha.1, hb.1]; push_cast; rfl, ?_⟩
  have := ha.2; have := hb.2; simp only [ops]; omega

theorem RunZ.mul (ha : RunZ W a env u ca) (hb : RunZ W b env v cb) :
    RunZ W (.mul a b) env (u * v) (1 + ca + cb) := by
  refine ⟨by rw [evalZ_mul, ha.1, hb.1]; push_cast; rfl, ?_⟩
  have := ha.2; have := hb.2; simp only [ops]; omega

/-! ### Loops -/

theorem RunZ.sum {F : ℕ → ℤ} (hn : Run W n env k cn) (hk : k ≤ T)
    (h : ∀ i < k, RunZ W b (i :: env) (F i) B) :
    RunZ W (.sum n b) env (∑ i ∈ range k, F i) (1 + cn + T * (B + 1)) := by
  refine ⟨?_, ?_⟩
  · rw [evalZ_sum, hn.1, Int.cast_sum]
    exact Finset.sum_congr rfl fun i hi => (h i (mem_range.mp hi)).1
  · have h1 := ops_sum_le W n b env (B := B) (fun i hi => (h i (by rwa [hn.1] at hi)).2)
    rw [hn.1] at h1
    have := hn.2
    have : k * (B + 1) ≤ T * (B + 1) := Nat.mul_le_mul_right _ hk
    omega

theorem RunZ.prod {F : ℕ → ℤ} (hn : Run W n env k cn) (hk : k ≤ T)
    (h : ∀ i < k, RunZ W b (i :: env) (F i) B) :
    RunZ W (.prod n b) env (∏ i ∈ range k, F i) (1 + cn + T * (B + 1)) := by
  refine ⟨?_, ?_⟩
  · rw [evalZ_prod, hn.1, Int.cast_prod]
    exact Finset.prod_congr rfl fun i hi => (h i (mem_range.mp hi)).1
  · have h1 := ops_prod_le W n b env (B := B) (fun i hi => (h i (by rwa [hn.1] at hi)).2)
    rw [hn.1] at h1
    have := hn.2
    have : k * (B + 1) ≤ T * (B + 1) := Nat.mul_le_mul_right _ hk
    omega

theorem RunZ.sumFin {F : Fin k → ℤ} (hn : Run W n env k cn) (hk : k ≤ T)
    (h : ∀ i : Fin k, RunZ W b ((i : ℕ) :: env) (F i) B) :
    RunZ W (.sum n b) env (∑ i, F i) (1 + cn + T * (B + 1)) := by
  rw [Code.sum_fin_eq_range]
  refine RunZ.sum hn hk fun i hi => ?_
  simpa [hi] using h ⟨i, hi⟩

theorem RunZ.prodFin {F : Fin k → ℤ} (hn : Run W n env k cn) (hk : k ≤ T)
    (h : ∀ i : Fin k, RunZ W b ((i : ℕ) :: env) (F i) B) :
    RunZ W (.prod n b) env (∏ i, F i) (1 + cn + T * (B + 1)) := by
  rw [Code.prod_fin_eq_range]
  refine RunZ.prod hn hk fun i hi => ?_
  simpa [hi] using h ⟨i, hi⟩

/-! ### Exact values of ring expressions -/

theorem eval_eq_of_cast {e : Expr} (hlt : eval W e env < 2 ^ W) {x : ℕ} (hx : x < 2 ^ W)
    (h : evalZ W e env = (x : ZMod (2 ^ W))) : eval W e env = x := by
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hx] at this

theorem RunZ.exact_add (h : RunZ W (.add a b) env (x : ℤ) ca) (hx : x < 2 ^ W) :
    Run W (.add a b) env x ca := by
  refine ⟨eval_eq_of_cast (by simp only [eval]; exact Nat.mod_lt _ (by positivity)) hx ?_, h.2⟩
  simpa using h.1

theorem RunZ.exact_sum (h : RunZ W (.sum a b) env (x : ℤ) ca) (hx : x < 2 ^ W) :
    Run W (.sum a b) env x ca := by
  refine ⟨eval_eq_of_cast (by rw [eval_sum]; exact Nat.mod_lt _ (by positivity)) hx ?_, h.2⟩
  simpa using h.1

/-- An exact sum of exact bodies. -/
theorem Run.sum {F : ℕ → ℕ} (hn : Run W n env k cn) (hk : k ≤ T)
    (h : ∀ i < k, Run W b (i :: env) (F i) B) (hlt : ∑ i ∈ range k, F i < 2 ^ W) :
    Run W (.sum n b) env (∑ i ∈ range k, F i) (1 + cn + T * (B + 1)) := by
  have h1 := RunZ.sum (F := fun i => (F i : ℤ)) hn hk fun i hi => (h i hi).toZ
  refine RunZ.exact_sum (h1.eq ?_) hlt
  push_cast
  rfl

/-! ### The de Bruijn shift -/

/-- Shift the variables at or above `d` by `k`. -/
def liftE (d k : ℕ) : Expr → Expr
  | .var i => if i < d then .var i else .var (i + k)
  | .lit n => .lit n
  | .add a b => .add (liftE d k a) (liftE d k b)
  | .sub a b => .sub (liftE d k a) (liftE d k b)
  | .mul a b => .mul (liftE d k a) (liftE d k b)
  | .div a b => .div (liftE d k a) (liftE d k b)
  | .mod a b => .mod (liftE d k a) (liftE d k b)
  | .pow2 a => .pow2 (liftE d k a)
  | .ite a b c e => .ite (liftE d k a) (liftE d k b) (liftE d k c) (liftE d k e)
  | .letE a b => .letE (liftE d k a) (liftE (d + 1) k b)
  | .fold n s b => .fold (liftE d k n) (liftE d k s) (liftE (d + 2) k b)
  | .sum n b => .sum (liftE d k n) (liftE (d + 1) k b)
  | .prod n b => .prod (liftE d k n) (liftE (d + 1) k b)
  | .sumIter n s f b => .sumIter (liftE d k n) (liftE d k s) (liftE (d + 1) k f) (liftE (d + 1) k b)

theorem getD_lift (pre mid post : List ℕ) (i : ℕ) :
    (pre ++ mid ++ post).getD (if i < pre.length then i else i + mid.length) 0 =
      (pre ++ post).getD i 0 := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_left, h]
  · have h' : pre.length ≤ i := not_lt.mp h
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right h',
      List.getElem?_append_right (by omega)]
    congr 2
    omega

theorem eval_liftE (e : Expr) (pre mid post : List ℕ) :
    eval W (liftE pre.length mid.length e) (pre ++ mid ++ post) = eval W e (pre ++ post) := by
  induction e generalizing pre with
  | var i =>
    have := getD_lift pre mid post i
    unfold liftE
    split_ifs at this ⊢ <;> simpa [eval] using this
  | lit n => rfl
  | add a b iha ihb => simp only [liftE, eval, iha, ihb]
  | sub a b iha ihb => simp only [liftE, eval, iha, ihb]
  | mul a b iha ihb => simp only [liftE, eval, iha, ihb]
  | div a b iha ihb => simp only [liftE, eval, iha, ihb]
  | mod a b iha ihb => simp only [liftE, eval, iha, ihb]
  | pow2 a iha => simp only [liftE, eval, iha]
  | ite a b c e iha ihb ihc ihe => simp only [liftE, eval, iha, ihb, ihc, ihe]
  | letE a b iha ihb =>
    simp only [liftE, eval, iha]
    exact ihb (eval W a (pre ++ post) :: pre)
  | fold n s b ihn ihs ihb =>
    simp only [liftE, eval, ihn, ihs]
    congr 1
    funext st k
    exact ihb (st :: k :: pre)
  | sum n b ihn ihb =>
    simp only [liftE, eval, ihn]
    congr 1
    funext st k
    congr 1
    congr 1
    exact ihb (k :: pre)
  | prod n b ihn ihb =>
    simp only [liftE, eval, ihn]
    congr 1
    funext st k
    congr 2
    exact ihb (k :: pre)
  | sumIter n s f b ihn ihs ihf ihb =>
    simp only [liftE, eval, ihn, ihs]
    congr 2
    funext p _
    rw [show eval W (liftE (pre.length + 1) mid.length f) (p.1 :: (pre ++ mid ++ post)) =
        eval W f (p.1 :: (pre ++ post)) from ihf (p.1 :: pre),
      show eval W (liftE (pre.length + 1) mid.length b) (p.1 :: (pre ++ mid ++ post)) =
        eval W b (p.1 :: (pre ++ post)) from ihb (p.1 :: pre)]

theorem ops_liftE (e : Expr) (pre mid post : List ℕ) :
    ops W (liftE pre.length mid.length e) (pre ++ mid ++ post) = ops W e (pre ++ post) := by
  induction e generalizing pre with
  | var i =>
    unfold liftE
    split_ifs <;> rfl
  | lit n => rfl
  | add a b iha ihb => simp only [liftE, ops, iha, ihb]
  | sub a b iha ihb => simp only [liftE, ops, iha, ihb]
  | mul a b iha ihb => simp only [liftE, ops, iha, ihb]
  | div a b iha ihb => simp only [liftE, ops, iha, ihb]
  | mod a b iha ihb => simp only [liftE, ops, iha, ihb]
  | pow2 a iha => simp only [liftE, ops, iha]
  | ite a b c e iha ihb ihc ihe => simp only [liftE, ops, iha, ihb, ihc, ihe, eval_liftE]
  | letE a b iha ihb =>
    simp only [liftE, ops, iha, eval_liftE]
    rw [show ops W (liftE (pre.length + 1) mid.length b) (eval W a (pre ++ post) :: (pre ++ mid ++ post)) =
        ops W b (eval W a (pre ++ post) :: (pre ++ post)) from ihb (eval W a (pre ++ post) :: pre)]
  | fold n s b ihn ihs ihb =>
    simp only [liftE, ops, ihn, ihs, eval_liftE]
    congr 2
    funext p k
    rw [show eval W (liftE (pre.length + 2) mid.length b) (p.1 :: k :: (pre ++ mid ++ post)) =
        eval W b (p.1 :: k :: (pre ++ post)) from eval_liftE b (p.1 :: k :: pre) mid post,
      show ops W (liftE (pre.length + 2) mid.length b) (p.1 :: k :: (pre ++ mid ++ post)) =
        ops W b (p.1 :: k :: (pre ++ post)) from ihb (p.1 :: k :: pre)]
  | sum n b ihn ihb =>
    simp only [liftE, ops, ihn, eval_liftE]
    congr 2
    refine List.map_congr_left fun k _ => ?_
    rw [show ops W (liftE (pre.length + 1) mid.length b) (k :: (pre ++ mid ++ post)) =
        ops W b (k :: (pre ++ post)) from ihb (k :: pre)]
  | prod n b ihn ihb =>
    simp only [liftE, ops, ihn, eval_liftE]
    congr 2
    refine List.map_congr_left fun k _ => ?_
    rw [show ops W (liftE (pre.length + 1) mid.length b) (k :: (pre ++ mid ++ post)) =
        ops W b (k :: (pre ++ post)) from ihb (k :: pre)]
  | sumIter n s f b ihn ihs ihf ihb =>
    simp only [liftE, ops, ihn, ihs, eval_liftE]
    congr 2
    funext p _
    rw [show eval W (liftE (pre.length + 1) mid.length f) (p.1 :: (pre ++ mid ++ post)) =
        eval W f (p.1 :: (pre ++ post)) from eval_liftE f (p.1 :: pre) mid post,
      show ops W (liftE (pre.length + 1) mid.length f) (p.1 :: (pre ++ mid ++ post)) =
        ops W f (p.1 :: (pre ++ post)) from ihf (p.1 :: pre),
      show ops W (liftE (pre.length + 1) mid.length b) (p.1 :: (pre ++ mid ++ post)) =
        ops W b (p.1 :: (pre ++ post)) from ihb (p.1 :: pre)]

/-- A program of the environment `pre ++ post` runs in `pre ++ mid ++ post` after the shift. -/
theorem RunZ.lift {e : Expr} {pre mid post : List ℕ}
    (h : RunZ W e (pre ++ post) u ca) :
    RunZ W (liftE pre.length mid.length e) (pre ++ mid ++ post) u ca := by
  refine ⟨?_, ?_⟩
  · simp only [evalZ, eval_liftE]; exact h.1
  · rw [ops_liftE]; exact h.2

/-! ### Sum iteration -/

theorem RunZ.sumIter {F : ℕ → ℤ} (hn : Run W n env k cn) (hs : Run W s env x cc) (hk : k ≤ T)
    (h : ∀ i < k, RunZ W b (iterate W f x env i :: env) (F i) B ∧
      ops W f (iterate W f x env i :: env) ≤ cd) :
    RunZ W (.sumIter n s f b) env (∑ i ∈ range k, F i) (1 + cn + cc + T * (B + cd + 1)) := by
  refine ⟨?_, ?_⟩
  · rw [evalZ_sumIter, hn.1, hs.1, Int.cast_sum]
    exact Finset.sum_congr rfl fun i hi => (h i (mem_range.mp hi)).1.1
  · have h1 := ops_sumIter_le W n s f b env (B := B + cd) (fun i hi => by
      rw [hs.1]
      rw [hn.1] at hi
      have := (h i hi).1.2
      have := (h i hi).2
      omega)
    rw [hn.1] at h1
    have := hn.2
    have := hs.2
    have : k * (B + cd + 1) ≤ T * (B + cd + 1) := Nat.mul_le_mul_right _ hk
    omega

/-! ### Powers, digits and bits -/

theorem Run.powE {bi i : ℕ} (hb : env.getD bi 0 = x) (hi : env.getD i 0 = y) (hy : y ≤ T)
    (h : x ^ y < 2 ^ W) : Run W (powE bi i) env (x ^ y) (2 + T * 2) := by
  refine ⟨by rw [eval_powE, hb, hi, Nat.mod_eq_of_lt h], ?_⟩
  have := ops_powE W bi i env
  rw [hi] at this
  omega

theorem Run.digE {ki gi i : ℕ} (hk : env.getD ki 0 = x) (hg : env.getD gi 0 = z)
    (hi : env.getD i 0 = y) (hy : y ≤ T) (h : z ^ y < 2 ^ W) :
    Run W (digE ki gi i) env (Code.dig z x y) (6 + T * 2) := by
  refine ⟨by rw [eval_digE W _ _ _ _ (by rw [hg, hi]; exact h), hk, hg, hi]; rfl, ?_⟩
  have := ops_digE W ki gi i env
  rw [hi] at this
  omega

/-- Bit `i` of the variable `k`, for an expression `i`. -/
def bitX (ki : ℕ) (i : Expr) : Expr := .mod (.div (.var ki) (.pow2 i)) (.lit 2)

theorem Run.bitX {ki : ℕ} {i : Expr} (hk : env.getD ki 0 = x) (hi : Run W i env y ca) (hy : y < W)
    (hW : 2 ≤ W) : Run W (bitX ki i) env (x.testBit y).toNat (5 + ca) := by
  have h2 : (2 : ℕ) < 2 ^ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have := Run.mod (Run.div (Run.var hk) (Run.pow2 hi hy)) (Run.lit (env := env) h2)
  refine (this.eq ?_).mono (by omega)
  rw [Nat.testBit_eq_decide_div_mod_eq]
  generalize x / 2 ^ y = q
  rcases Nat.mod_two_eq_zero_or_one q with hz | hz <;> simp [hz]

end TransposeBase.Pseudo.Leaf
