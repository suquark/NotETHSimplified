import UncrossingWires.Pseudo.Frame

/-!
# The programs of the two factors of a rectangle

Each helper of `UncrossingWires/Pseudo/Prog.lean` gets one statement `Run` (an exact value) or `RunZ` (a value in the ring of
words), with a cost that is an explicit function of the scale `sc`. A Boolean is held as `b.toNat` in a variable.
-/

namespace UncrossingWires.Pseudo

open Finset TransposeBase.Pseudo TransposeBase.Pseudo.Leaf

/-- The bound on the operations of a factor of a rectangle, for the scale `sc`. -/
def rectCost (sc : ℕ) : ℕ := 20000 * (sc + 1) ^ 2

/-- The word size is large enough for the factors of a rectangle. -/
structure RectBig (W sc bk : ℕ) : Prop where
  sizes : Lag.Sizes W sc bk
  hW : 8 * sc + 8 < W

namespace Rect

variable {W sc bk : ℕ} {env : List ℕ}

/-! ### Small numbers -/

/-- A variable of an environment, under one more binder. -/
theorem up {env : List ℕ} {x i v : ℕ} (h : env.getD i 0 = v) : (x :: env).getD (i + 1) 0 = v := h

theorem small_lt {x W : ℕ} (h : x < W) : x < 2 ^ W := lt_trans h Nat.lt_two_pow_self

/-- A literal below the word length has its exact value. -/
theorem run_lit {x : ℕ} (h : x < W) : Run W (.lit x) env x 1 := Run.lit (small_lt h)

/-- `3 ^ k` fits in the word as soon as `2 * k` is below the word length. -/
theorem three_pow_lt {k W : ℕ} (h : 2 * k < W) : 3 ^ k < 2 ^ W := by
  calc 3 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
    _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
    _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) h

theorem toNat_eq_iff {A B : Bool} : A.toNat = B.toNat ↔ A = B := by
  cases A <;> cases B <;> simp

theorem popB_le (M j : ℕ) : popB M j ≤ j := by
  unfold popB
  calc ∑ i ∈ range j, (M.testBit i).toNat ≤ ∑ _i ∈ range j, 1 :=
        sum_le_sum fun i _ => Bool.toNat_le _
    _ = j := by simp

theorem cnt_le (m : ℕ) (π : ℕ → ℕ) (l : ℕ) : cnt m π l ≤ m := by
  unfold cnt
  calc ∑ j ∈ range m, (if π j = l then 1 else 0) ≤ ∑ _j ∈ range m, 1 :=
        sum_le_sum fun j _ => by split_ifs <;> omega
    _ = m := by simp

theorem sizes_mono {W sc k n : ℕ} (h : Lag.Sizes W sc k) (hn : n ≤ sc) : Lag.Sizes W n k where
  hk := lt_of_le_of_lt (Nat.factorial_le (by omega)) h.hk
  hn := by have := h.hn; omega
  hw := lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) h.hw
  hk1 := h.hk1

/-! ### `popBE`, `pow3E` -/

theorem run_popBE {T iM ij M j : ℕ} (hW : 2 ≤ W) (hjW : j < W) (hjT : j ≤ T)
    (hM : env.getD iM 0 = M) (hj : env.getD ij 0 = j) :
    Run W (popBE iM ij) env (popB M j) (2 + T * 7) := by
  have h := Run.sum (W := W) (env := env) (F := fun i => (M.testBit i).toNat)
    (b := bitX (iM + 1) (.var 0)) (B := 6) (Run.var hj) hjT
    (fun i hi => Run.bitX (ca := 1) hM (Run.var rfl) (by omega) hW)
    (lt_of_le_of_lt (popB_le M j) (small_lt hjW))
  exact Run.mono h (by omega)

theorem run_pow3E {T k ce : ℕ} {e : Expr} (hW : 4 ≤ W) (he : Run W e env k ce) (hkT : k ≤ T)
    (hlt : 3 ^ k < 2 ^ W) :
    Run W (pow3E e) env (3 ^ k) (1 + ce + T * 2) := by
  refine ⟨?_, ?_⟩
  · have h3 : ∀ i, eval W (.lit 3) (i :: env) = 3 := fun i =>
      (run_lit (W := W) (x := 3) (env := i :: env) (by omega)).1
    rw [pow3E, eval_prod, he.1, prod_congr rfl (fun i _ => h3 i), prod_const, card_range,
      Nat.mod_eq_of_lt hlt]
  · have h1 := ops_prod_le W e (.lit 3) env (B := 1) (fun _ _ => le_rfl)
    rw [he.1] at h1
    have h2 := he.2
    have h3 : k * (1 + 1) ≤ T * 2 := Nat.mul_le_mul_right _ hkT
    unfold pow3E
    omega

/-! ### `letterE` -/

/-- A test of a direction, with two literals. -/
theorem run_dirIte {id a b : ℕ} {dir : Bool} (hW : 1 ≤ W) (hd : env.getD id 0 = dir.toNat)
    (ha : a < W) (hb : b < W) :
    Run W (.ite (.var id) (.lit 0) (.lit a) (.lit b)) env (if dir then b else a) 5 := by
  refine Run.mono (Run.ite (Run.var hd) (run_lit (x := 0) (by omega))
    (fun h => (run_lit ha).eq ?_) (fun h => (run_lit hb).eq ?_)) (by omega)
  · cases dir <;> simp_all
  · cases dir <;> simp_all

/-- The operations of `letterE`. -/
def letterCost (sc : ℕ) : ℕ := 60 + 9 * sc

theorem run_letterE {ic id im ixi ij : ℕ} {cheap dir : Bool} {m ξ j : ℕ} (hW : 8 * sc + 8 < W)
    (hmsc : m ≤ sc) (hc : env.getD ic 0 = cheap.toNat) (hd : env.getD id 0 = dir.toNat)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) (hj : env.getD ij 0 = j) :
    Run W (letterE ic id im ixi ij) env (letterOf cheap dir m ξ j) (letterCost sc) := by
  have hmW : m < W := by omega
  -- the plain code
  have hplain : j < m → Run W (.mod (.div (.var ixi) (.pow2 (.mul (.lit 2) (.var ij)))) (.lit 4)) env
      (letterPlain ξ j) 8 := by
    intro hjm
    have h2j : 2 * j < W := by omega
    have h := Run.mod (Run.div (Run.var (W := W) hx)
      (Run.pow2 (Run.mul (run_lit (x := 2) (by omega)) (Run.var hj) (small_lt h2j)) h2j))
      (run_lit (x := 4) (by omega))
    exact (Run.mono h (by omega)).eq (by rw [letterPlain, pow_mul]; norm_num)
  -- the short code
  have hcheap : j < m → Run W (.letE (.mod (.var ixi) (.pow2 (.var im))) <|
        .ite (bitX 0 (.var (ij + 1))) (.lit 0)
          (.add
            (.mod (.div (.div (.var (ixi + 1)) (.pow2 (.var (im + 1))))
              (pow3E (.sub (.var (ij + 1)) (popBE 0 (ij + 1))))) (.lit 3))
            (.ite (.var (id + 1)) (.lit 0) (.lit 1) (.lit 0)))
          (.ite (.var (id + 1)) (.lit 0) (.lit 0) (.lit 3))) env (letterCheap dir m ξ j)
      (36 + 9 * sc) := by
    intro hjm
    have hjW : j < W := by omega
    have hsc1 : j ≤ sc := by omega
    have hM := Run.mod (Run.var (W := W) hx) (Run.pow2 (Run.var hm) hmW)
    generalize hMdef : ξ % 2 ^ m = M at hM
    have hsub : Run W (.sub (.var (ij + 1)) (popBE 0 (ij + 1))) (M :: env) (j - popB M j)
        (1 + 1 + (2 + sc * 7)) :=
      Run.sub (Run.var hj) (run_popBE (T := sc) (by omega) hjW hsc1 rfl hj) (small_lt hjW) (popB_le M j)
    have hk : j - popB M j ≤ sc := by omega
    have hpow := run_pow3E (T := sc) (by omega) hsub hk (three_pow_lt (by omega))
    have hdig := Run.mod (Run.div (Run.div (Run.var (W := W) (up (x := M) hx))
      (Run.pow2 (Run.var (up hm)) hmW)) hpow) (run_lit (x := 3) (by omega))
    have hoff : Run W (.ite (.var (id + 1)) (.lit 0) (.lit 1) (.lit 0)) (M :: env)
        (if dir then 0 else 1) 5 := run_dirIte (by omega) hd (by omega) (by omega)
    have hspec : Run W (.ite (.var (id + 1)) (.lit 0) (.lit 0) (.lit 3)) (M :: env)
        (if dir then 3 else 0) 5 := run_dirIte (by omega) hd (by omega) (by omega)
    have hadd := Run.add hdig hoff (by
      have h1 := Nat.mod_lt (ξ / 2 ^ m / 3 ^ (j - popB M j)) (by norm_num : 3 > 0)
      have h2 : (if dir then 0 else 1) ≤ 1 := by split_ifs <;> omega
      have h3 : (4 : ℕ) < 2 ^ W := small_lt (by omega)
      omega)
    refine Run.mono (Run.letE hM (Run.ite (Run.bitX rfl (Run.var hj) hjW (by omega))
      (run_lit (x := 0) (by omega)) (fun h => hadd.eq ?_) (fun h => hspec.eq ?_))) ?_
    · have hb : M.testBit j = false := by cases hbit : M.testBit j <;> simp_all
      rw [letterCheap, hMdef, hb]
      simp
    · have hb : M.testBit j = true := by cases hbit : M.testBit j <;> simp_all
      rw [letterCheap, hMdef, hb]
      simp
    · omega
  refine Run.mono (Run.ite (Run.var hm) (Run.var hj) (r := letterOf cheap dir m ξ j)
    (fun h => (run_lit (x := 0) (by omega)).eq ?_)
    (fun h => Run.ite (Run.var hc) (run_lit (x := 0) (by omega))
      (fun h1 => (hplain (by omega)).eq ?_) (fun h1 => (hcheap (by omega)).eq ?_))) ?_
  · rw [letterOf, if_neg (by omega)]
  · have : cheap = false := by cases cheap <;> simp_all
    rw [letterOf, if_pos (by omega), this]
    simp
  · have : cheap = true := by cases cheap <;> simp_all
    rw [letterOf, if_pos (by omega), this]
    simp
  · unfold letterCost
    omega

/-! ### `chiE`, `fpatE`, `cntE` -/

/-- A test of equality of two Booleans given by expressions. -/
theorem runZ_eqXb {a b c d : Expr} {A B : Bool} {u v : ℤ} {ca cb cc cd : ℕ}
    (ha : Run W a env A.toNat ca) (hb : Run W b env B.toNat cb)
    (hc : RunZ W c env u cc) (hd : RunZ W d env v cd) :
    RunZ W (eqX a b c d) env (if A = B then u else v) (2 + 2 * (ca + cb) + 2 * (cc + cd)) :=
  RunZ.eqX ha hb (fun h => hc.eq (if_pos (toNat_eq_iff.mp h)).symm)
    (fun h => hd.eq (if_neg fun e => h (toNat_eq_iff.mpr e)).symm)

theorem runZ_chiE {il l ca cb : ℕ} {a b : Expr} {A B : Bool} (hW : 4 ≤ W)
    (hl : env.getD il 0 = l) (ha : Run W a env A.toNat ca) (hb : Run W b env B.toNat cb) :
    RunZ W (chiE il a b) env (chi l A B) (53 + 12 * ca + 8 * cb) := by
  have hsg : RunZ W (.ite a (.lit 0) (.lit 1) (.sub (.lit 0) (.lit 1))) env (if A then -1 else 1)
      (6 + ca) := by
    refine RunZ.mono (RunZ.ite ha (run_lit (x := 0) (by omega))
      (fun h => RunZ.lit1.eq ?_) (fun h => (RunZ.sub RunZ.lit0 RunZ.lit1).eq ?_)) (by omega)
    · cases A <;> simp_all
    · cases A <;> simp_all
  have e1 := runZ_eqXb ha hb (RunZ.lit1 (env := env)) (RunZ.lit0 (env := env))
  have e2 := runZ_eqXb ha hb (RunZ.lit0 (env := env)) (RunZ.lit1 (env := env))
  have e3 := runZ_eqXb ha hb hsg (RunZ.lit0 (env := env))
  have e4 := runZ_eqXb ha hb (RunZ.lit0 (env := env)) hsg
  refine RunZ.mono (RunZ.ite (Run.var hl) (run_lit (x := 0) (by omega))
    (fun h0 => e1.eq ?_)
    (fun h0 => RunZ.ite (Run.var hl) (run_lit (x := 1) (by omega))
      (fun h1 => e2.eq ?_)
      (fun h1 => RunZ.ite (Run.var hl) (run_lit (x := 2) (by omega))
        (fun h2 => e3.eq ?_) (fun h2 => e4.eq ?_)))) ?_
  · obtain rfl : l = 0 := by omega
    rfl
  · obtain rfl : l = 1 := by omega
    rfl
  · obtain rfl : l = 2 := by omega
    rfl
  · obtain ⟨n, rfl⟩ : ∃ n, l = n + 3 := ⟨l - 3, by omega⟩
    rfl
  · omega

/-- The operations of `fpatE`. -/
def fpatCost (sc : ℕ) : ℕ := 2 + sc * (175 + letterCost sc)

theorem runZ_fpatE {ic id im ixi ip iq : ℕ} {cheap dir : Bool} {m ξ p q : ℕ} (hW : 8 * sc + 8 < W)
    (hmsc : m ≤ sc) (hc : env.getD ic 0 = cheap.toNat) (hd : env.getD id 0 = dir.toNat)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) (hp : env.getD ip 0 = p)
    (hq : env.getD iq 0 = q) :
    RunZ W (fpatE ic id im ixi ip iq) env (fpat m (letterOf cheap dir m ξ) p q) (fpatCost sc) := by
  have hbody : ∀ j < m, RunZ W (.letE (letterE (ic + 1) (id + 1) (im + 1) (ixi + 1) 0) <|
      chiE 0 (bitX (ip + 2) (.var 1)) (bitX (iq + 2) (.var 1))) (j :: env)
      (chi (letterOf cheap dir m ξ j) (p.testBit j) (q.testBit j)) (1 + letterCost sc + 173) := by
    intro j hj
    have hL := run_letterE (W := W) (ij := 0) (j := j) (env := j :: env) hW hmsc (up hc) (up hd) (up hm)
      (up hx) rfl
    have hbp := Run.bitX (W := W) (env := letterOf cheap dir m ξ j :: j :: env) (up (up hp))
      (Run.var (up (x := letterOf cheap dir m ξ j) (i := 0) (v := j) rfl)) (by omega) (by omega)
    have hbq := Run.bitX (W := W) (env := letterOf cheap dir m ξ j :: j :: env) (up (up hq))
      (Run.var (up (x := letterOf cheap dir m ξ j) (i := 0) (v := j) rfl)) (by omega) (by omega)
    exact RunZ.mono (RunZ.letE hL (runZ_chiE (by omega) rfl hbp hbq)) (by omega)
  refine RunZ.mono (RunZ.prod (Run.var hm) hmsc hbody) ?_
  unfold fpatCost
  have : sc * (1 + letterCost sc + 173 + 1) = sc * (175 + letterCost sc) := by ring
  omega

/-- The operations of `cntE`. -/
def cntCost (sc : ℕ) : ℕ := 2 + sc * (12 + letterCost sc)

theorem run_cntE {ic id im ixi l : ℕ} {cheap dir : Bool} {m ξ : ℕ} (hW : 8 * sc + 8 < W)
    (hmsc : m ≤ sc) (hl : l < W) (hc : env.getD ic 0 = cheap.toNat) (hd : env.getD id 0 = dir.toNat)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) :
    Run W (cntE ic id im ixi l) env (cnt m (letterOf cheap dir m ξ) l) (cntCost sc) := by
  have hbody : ∀ j < m, Run W (.letE (letterE (ic + 1) (id + 1) (im + 1) (ixi + 1) 0) <|
      eqX (.var 0) (.lit l) (.lit 1) (.lit 0)) (j :: env)
      (if letterOf cheap dir m ξ j = l then 1 else 0) (1 + letterCost sc + 10) := by
    intro j hj
    have hL := run_letterE (W := W) (ij := 0) (j := j) (env := j :: env) hW hmsc (up hc) (up hd) (up hm)
      (up hx) rfl
    refine Run.mono (Run.letE hL (Run.eqX (Run.var rfl) (run_lit hl)
      (fun h => (run_lit (x := 1) (by omega)).eq (if_pos h).symm)
      (fun h => (run_lit (x := 0) (by omega)).eq (if_neg h).symm))) (by omega)
  have hlt : ∑ j ∈ range m, (if letterOf cheap dir m ξ j = l then 1 else 0) < 2 ^ W :=
    lt_of_le_of_lt (cnt_le m _ l) (small_lt (by omega))
  refine Run.mono (Run.sum (Run.var hm) hmsc hbody hlt) ?_
  unfold cntCost
  have : sc * (1 + letterCost sc + 10 + 1) = sc * (12 + letterCost sc) := by ring
  omega

/-! ### `condE`, `signE`, the binomials -/

theorem runZ_condE {ipol im ir m r cc cd : ℕ} {pol : Bool} {c d : Expr} {u v : ℤ} (hW : 4 ≤ W)
    (hmW : m + 1 < W) (hpol : env.getD ipol 0 = pol.toNat) (hm : env.getD im 0 = m)
    (hr : env.getD ir 0 = r) (hc : RunZ W c env u cc) (hd : RunZ W d env v cd) :
    RunZ W (condE ipol im ir c d) env (if condP pol m r then u else v) (17 + 2 * (cc + cd)) := by
  have ht : Run W (.div (.add (.var im) (.lit 1)) (.lit 2)) env (thr m) 5 :=
    Run.mono (Run.div (Run.add (Run.var hm) (run_lit (x := 1) (by omega)) (small_lt hmW))
      (run_lit (x := 2) (by omega))) (by omega)
  have h1 : RunZ W (.ite (.div (.add (.var im) (.lit 1)) (.lit 2)) (.var ir) d c) env
      (if r < thr m then u else v) (1 + 5 + 1 + (cd + cc)) :=
    RunZ.ite ht (Run.var hr) (fun h => hd.eq (if_neg (by omega)).symm)
      (fun h => hc.eq (if_pos (by omega)).symm)
  have h2 : RunZ W (.ite (.div (.add (.var im) (.lit 1)) (.lit 2)) (.var ir) c d) env
      (if thr m ≤ r then u else v) (1 + 5 + 1 + (cc + cd)) :=
    RunZ.ite ht (Run.var hr) (fun h => hc.eq (if_pos h).symm) (fun h => hd.eq (if_neg h).symm)
  refine RunZ.mono (RunZ.ite (Run.var hpol) (run_lit (x := 0) (by omega))
    (fun h => h1.eq ?_) (fun h => h2.eq ?_)) (by omega)
  · have : pol = false := by cases pol <;> simp_all
    subst this
    simp [condP]
  · have : pol = true := by cases pol <;> simp_all
    subst this
    simp [condP]

theorem runZ_signE {ir r : ℕ} (hW : 4 ≤ W) (hr : env.getD ir 0 = r) :
    RunZ W (signE ir) env ((-1) ^ r) 9 := by
  refine RunZ.mono (RunZ.ite (Run.mod (Run.var hr) (run_lit (x := 2) (by omega)))
    (run_lit (x := 0) (by omega)) (fun h => RunZ.lit1.eq ?_)
    (fun h => (RunZ.sub RunZ.lit0 RunZ.lit1).eq ?_)) (by omega)
  · have : Even r := Nat.even_iff.mpr (by omega)
    rw [this.neg_one_pow]
  · have : Odd r := Nat.odd_iff.mpr (by omega)
    rw [this.neg_one_pow]
    norm_num

theorem run_chooseE {N B b n k r : ℕ} (h : Lag.Sizes W n k) (hN : env.getD N 0 = n)
    (hB : env.getD B 0 = k) (hb : env.getD b 0 = r) (hr : r ≤ n + 1) :
    Run W (Lag.chooseE N B b) env (n.choose r) (10 + 5 * n) := by
  refine ⟨?_, ?_⟩
  · rw [Lag.eval_chooseE h hN hB (b := b) (by rw [hb]; exact hr), hb]
  · have h2 : ops W (.prod (.var N) (.add (.pow2 (.var (B + 1))) (.lit 1))) env ≤ 2 + n * 5 := by
      have := ops_prod_le W (.var N) (.add (.pow2 (.var (B + 1))) (.lit 1)) env (B := 4)
        (fun j _ => by simp [ops])
      have hn : eval W (.var N) env = n := hN
      rw [hn] at this
      have h3 : ops W (.var N) env = 1 := rfl
      omega
    have e1 : ops W (Lag.chooseE N B b) env =
        ops W (.prod (.var N) (.add (.pow2 (.var (B + 1))) (.lit 1))) env + 8 :=
      Lag.ops_fieldE _ _ _
    omega

/-! ### The coefficients -/

/-- The operations of `coefRE`. -/
def coefRCost (sc : ℕ) : ℕ := 4 + (sc + 1) * (66 + 10 * sc)

theorem runZ_coefRE {ipol im in3 ibk m n3 : ℕ} {pol : Bool} (hB : RectBig W sc bk)
    (hpol : env.getD ipol 0 = pol.toNat) (hm : env.getD im 0 = m) (hn3 : env.getD in3 0 = n3)
    (hbk : env.getD ibk 0 = bk) (hmsc : m ≤ sc) (hn3sc : n3 ≤ sc) :
    RunZ W (coefRE ipol im in3 ibk) env (coefR pol m n3) (coefRCost sc) := by
  have hW := hB.hW
  have hS : Lag.Sizes W n3 bk := sizes_mono hB.sizes hn3sc
  have hbody : ∀ r < n3 + 1, RunZ W (condE (ipol + 1) (im + 1) 0
      (.mul (.mul (Lag.chooseE (in3 + 1) (ibk + 1) 0) (signE 0)) (.pow2 (.var 0))) (.lit 0)) (r :: env)
      (if condP pol m r then (n3.choose r : ℤ) * (-2) ^ r else 0) (65 + 10 * sc) := by
    intro r hr
    have hr0 : (r :: env).getD 0 0 = r := rfl
    have hc := RunZ.mul (RunZ.mul (run_chooseE (r := r) hS (up hn3) (up hbk) hr0 (by omega)).toZ
      (runZ_signE (r := r) (by omega) hr0)) (Run.pow2 (Run.var hr0) (by omega)).toZ
    have hc' : RunZ W (.mul (.mul (Lag.chooseE (in3 + 1) (ibk + 1) 0) (signE 0)) (.pow2 (.var 0)))
        (r :: env) ((n3.choose r : ℤ) * (-2) ^ r) (23 + 5 * n3) := by
      refine RunZ.mono (hc.eq ?_) (by omega)
      have : (-2 : ℤ) ^ r = (-1) ^ r * 2 ^ r := by rw [← mul_pow]; norm_num
      rw [this]
      push_cast
      ring
    refine RunZ.mono (runZ_condE (r := r) (by omega) (by omega) (up hpol) (up hm) rfl hc' RunZ.lit0)
      (by omega)
  refine RunZ.mono (RunZ.sum (T := sc + 1)
    (Run.add (Run.var hn3) (run_lit (x := 1) (by omega)) (small_lt (by omega))) (by omega) hbody) ?_
  unfold coefRCost
  have : (sc + 1) * (65 + 10 * sc + 1) = (sc + 1) * (66 + 10 * sc) := by ring
  omega

/-- The operations of `coefCE`. -/
def coefCCost (sc : ℕ) : ℕ := 14 + (sc + 1) * (76 + 10 * sc)

theorem runZ_coefCE {ipol im in0 in3 ibk m n0 n3 : ℕ} {pol : Bool} (hB : RectBig W sc bk)
    (hpol : env.getD ipol 0 = pol.toNat) (hm : env.getD im 0 = m) (hn0 : env.getD in0 0 = n0)
    (hn3 : env.getD in3 0 = n3) (hbk : env.getD ibk 0 = bk) (hmsc : m ≤ sc) (hn0m : n0 ≤ m) :
    RunZ W (coefCE ipol im in0 in3 ibk) env (coefC pol m n0 n3) (coefCCost sc) := by
  have hW := hB.hW
  have hS : Lag.Sizes W n0 bk := sizes_mono hB.sizes (by omega)
  have hbody : ∀ r < n0 + 1, RunZ W (.letE (.add (.sub (.var (im + 1)) (.var (in0 + 1))) (.var 0)) <|
        condE (ipol + 2) (im + 2) 0
          (.mul (.mul (Lag.chooseE (in0 + 2) (ibk + 2) 1) (.pow2 (.sub (.var (in0 + 2)) (.var 1))))
            (signE 1)) (.lit 0)) (r :: env)
      (if condP pol m (m - n0 + r) then (n0.choose r : ℤ) * 2 ^ (n0 - r) * (-1) ^ r else 0)
      (75 + 10 * sc) := by
    intro r hr
    have hx : Run W (.add (.sub (.var (im + 1)) (.var (in0 + 1))) (.var 0)) (r :: env) (m - n0 + r)
        5 := Run.mono (Run.add (Run.sub (Run.var (up hm)) (Run.var (up hn0))
          (small_lt (by omega)) hn0m) (Run.var rfl) (small_lt (by omega))) (by omega)
    have hr0 : ((m - n0 + r) :: r :: env).getD 1 0 = r := rfl
    have hc := RunZ.mul (RunZ.mul (run_chooseE (env := (m - n0 + r) :: r :: env) (r := r) hS
      (up (up hn0)) (up (up hbk)) hr0 (by omega)).toZ
      (Run.pow2 (Run.sub (Run.var (up (up hn0))) (Run.var hr0) (small_lt (by omega)) (by omega))
        (by omega)).toZ)
      (runZ_signE (r := r) (by omega) hr0)
    have hc' : RunZ W (.mul (.mul (Lag.chooseE (in0 + 2) (ibk + 2) 1)
        (.pow2 (.sub (.var (in0 + 2)) (.var 1)))) (signE 1)) ((m - n0 + r) :: r :: env)
        ((n0.choose r : ℤ) * 2 ^ (n0 - r) * (-1) ^ r) (25 + 5 * n0) := by
      refine RunZ.mono (hc.eq ?_) (by omega)
      push_cast
      ring
    exact RunZ.mono (RunZ.letE hx (runZ_condE (r := m - n0 + r) (by omega) (by omega) (up (up hpol))
      (up (up hm)) rfl hc' RunZ.lit0)) (by omega)
  have hs := RunZ.sum (T := sc + 1)
    (Run.add (Run.var hn0) (run_lit (x := 1) (by omega)) (small_lt (by omega))) (by omega) hbody
  refine RunZ.mono (RunZ.mul (runZ_signE (by omega) hn3) hs) ?_
  unfold coefCCost
  have : (sc + 1) * (75 + 10 * sc + 1) = (sc + 1) * (76 + 10 * sc) := by ring
  omega

/-- The operations of `rectCoefE`. -/
def rectCoefCost (sc : ℕ) : ℕ := 5 + 2 * cntCost sc + (coefCCost sc + coefRCost sc)

theorem runZ_rectCoefE {ic id ipol im ixi ibk m ξ : ℕ} {cheap dir pol : Bool} (hB : RectBig W sc bk)
    (hc : env.getD ic 0 = cheap.toNat) (hd : env.getD id 0 = dir.toNat)
    (hpol : env.getD ipol 0 = pol.toNat) (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ)
    (hbk : env.getD ibk 0 = bk) (hmsc : m ≤ sc) :
    RunZ W (rectCoefE ic id ipol im ixi ibk) env (rectCoef dir pol m (letterOf cheap dir m ξ))
      (rectCoefCost sc) := by
  have hW := hB.hW
  have h3 := run_cntE (env := env) (l := 3) hW hmsc (by omega) hc hd hm hx
  generalize hn3 : cnt m (letterOf cheap dir m ξ) 3 = n3 at h3
  have h0 := run_cntE (env := n3 :: env) (ic := ic + 1) (id := id + 1) (im := im + 1) (ixi := ixi + 1)
    (l := 0) hW hmsc (by omega) (up hc) (up hd) (up hm) (up hx)
  generalize hn0 : cnt m (letterOf cheap dir m ξ) 0 = n0 at h0
  have hn3m : n3 ≤ m := hn3 ▸ cnt_le _ _ _
  have hn0m : n0 ≤ m := hn0 ▸ cnt_le _ _ _
  have hC := runZ_coefCE (env := n0 :: n3 :: env) (ipol := ipol + 2) (im := im + 2) (in0 := 0) (in3 := 1)
    (ibk := ibk + 2) (n0 := n0) hB (up (up hpol)) (up (up hm)) rfl (up (x := n0) (i := 0) (v := n3) rfl)
    (up (up hbk)) hmsc hn0m
  have hR := runZ_coefRE (env := n0 :: n3 :: env) (ipol := ipol + 2) (im := im + 2) (in3 := 1)
    (ibk := ibk + 2) hB (up (up hpol)) (up (up hm)) (up (x := n0) (i := 0) (v := n3) rfl)
    (up (up hbk)) hmsc (by omega)
  refine RunZ.mono (RunZ.letE h3 (RunZ.letE h0 (RunZ.ite (Run.var (up (up hd)))
    (run_lit (x := 0) (by omega)) (fun h => hC.eq ?_) (fun h => hR.eq ?_)))) ?_
  · have : dir = false := by cases dir <;> simp_all
    subst this
    rw [rectCoef, hn3, hn0]
    simp
  · have : dir = true := by cases dir <;> simp_all
    subst this
    rw [rectCoef, hn3]
    simp
  · unfold rectCoefCost
    omega

/-! ### `validE` -/

/-- The operations of `validE`. -/
def validCost (sc : ℕ) : ℕ := 23 + 9 * sc

theorem run_validE {ic im ixi m ξ : ℕ} {cheap : Bool} (hW : 8 * sc + 8 < W) (hmsc : m ≤ sc)
    (hξ : ξ < 2 ^ (2 * sc)) (hc : env.getD ic 0 = cheap.toNat) (hm : env.getD im 0 = m)
    (hx : env.getD ixi 0 = ξ) :
    Run W (validE ic im ixi) env (if validIdx cheap m ξ then 1 else 0) (validCost sc) := by
  have hmW : m < W := by omega
  have hM := Run.mod (Run.var (W := W) hx) (Run.pow2 (Run.var hm) hmW)
  generalize hMdef : ξ % 2 ^ m = M at hM
  have hsub : Run W (.sub (.var (im + 1)) (popBE 0 (im + 1))) (M :: env) (m - popB M m)
      (1 + 1 + (2 + sc * 7)) :=
    Run.sub (Run.var (up hm)) (run_popBE (T := sc) (by omega) hmW hmsc rfl (up hm)) (small_lt hmW)
      (popB_le M m)
  have hk : m - popB M m ≤ sc := by omega
  have hpow := run_pow3E (T := sc) (by omega) hsub hk (three_pow_lt (by omega))
  have hdiv : ξ / 2 ^ m + 1 < 2 ^ W := by
    have h1 : ξ / 2 ^ m ≤ ξ := Nat.div_le_self _ _
    have h2 : 2 ^ (2 * sc) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hadd := Run.add (Run.div (Run.var (W := W) (up (x := M) hx)) (Run.pow2 (Run.var (up hm)) hmW))
    (run_lit (x := 1) (by omega)) hdiv
  have hin : Run W (.letE (.mod (.var ixi) (.pow2 (.var im))) <|
      .ite (.add (.div (.var (ixi + 1)) (.pow2 (.var (im + 1)))) (.lit 1))
        (pow3E (.sub (.var (im + 1)) (popBE 0 (im + 1)))) (.lit 1) (.lit 0)) env
      (if validIdx true m ξ then 1 else 0) (19 + 9 * sc) := by
    have hval : validIdx true m ξ ↔ ξ / 2 ^ m + 1 ≤ 3 ^ (m - popB M m) := by
      rw [validIdx, hMdef]
      simp only [true_implies]
      omega
    refine Run.mono (Run.letE hM (Run.ite hadd hpow
      (fun h => (run_lit (x := 1) (by omega)).eq (if_pos (hval.mpr h)).symm)
      (fun h => (run_lit (x := 0) (by omega)).eq (if_neg (fun e => h (hval.mp e))).symm))) (by omega)
  refine Run.mono (Run.ite (Run.var hc) (run_lit (x := 0) (by omega))
    (fun h => (run_lit (x := 1) (by omega)).eq ?_) (fun h => hin.eq ?_)) ?_
  · have : cheap = false := by cases cheap <;> simp_all
    subst this
    simp [validIdx]
  · have : cheap = true := by cases cheap <;> simp_all
    rw [this]
  · unfold validCost
    omega

/-- `cheap`, as a number. -/
theorem run_cheap {ipol id : ℕ} {pol dir : Bool} (hW : 4 ≤ W) (hpol : env.getD ipol 0 = pol.toNat)
    (hd : env.getD id 0 = dir.toNat) :
    Run W (eqX (.var ipol) (.var id) (.lit 1) (.lit 0)) env (pol == dir).toNat 10 := by
  refine Run.mono (Run.eqX (Run.var hpol) (Run.var hd)
    (fun h => (run_lit (x := 1) (by omega)).eq ?_) (fun h => (run_lit (x := 0) (by omega)).eq ?_))
    (by omega)
  · rw [toNat_eq_iff.mp h]
    simp
  · have : pol ≠ dir := fun e => h (e ▸ rfl)
    cases pol <;> cases dir <;> simp_all

end Rect

open Rect in
/-- **The first factor.** -/
theorem runZ_rectAE {W sc bk : ℕ} (hB : RectBig W sc bk) {env : List ℕ}
    {id ipol isc im ixi ip iq ibk : ℕ} {dir pol : Bool} {m ξ p q : ℕ}
    (hd : env.getD id 0 = dir.toNat) (hpol : env.getD ipol 0 = pol.toNat) (hs : env.getD isc 0 = sc)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) (hp : env.getD ip 0 = p) (hq : env.getD iq 0 = q)
    (hbk : env.getD ibk 0 = bk) (hmsc : m ≤ sc) (hξ : ξ < 2 ^ (2 * sc)) :
    RunZ W (rectAE id ipol isc im ixi ip iq ibk) env (rectA dir pol sc m ξ p q) (rectCost sc) := by
  have hW := hB.hW
  have hC := run_cheap (W := W) (env := env) (by omega) hpol hd
  generalize hcheap : (pol == dir) = cheap at hC
  have hc0 : (cheap.toNat :: env).getD 0 0 = cheap.toNat := rfl
  have hV := run_validE (W := W) (env := cheap.toNat :: env) (im := im + 1) (ixi := ixi + 1) hW hmsc hξ
    hc0 (up hm) (up hx)
  have hcoef := runZ_rectCoefE (env := cheap.toNat :: env) (id := id + 1) (ipol := ipol + 1) (im := im + 1)
    (ixi := ixi + 1) (ibk := ibk + 1) hB hc0 (up hd) (up hpol) (up hm) (up hx) (up hbk) hmsc
  have hfpat := runZ_fpatE (env := cheap.toNat :: env) (id := id + 1) (im := im + 1) (ixi := ixi + 1)
    (ip := ip + 1) (iq := iq + 1) hW hmsc hc0 (up hd) (up hm) (up hx) (up hp) (up hq)
  have hpow := Run.pow2 (Run.sub (W := W) (Run.var (up (x := cheap.toNat) hs))
    (Run.var (up (x := cheap.toNat) hm)) (small_lt (by omega)) hmsc) (by omega : sc - m < W)
  have hmul := RunZ.mul (RunZ.mul hpow.toZ hcoef) hfpat
  refine RunZ.mono (RunZ.letE hC (RunZ.ite hV (run_lit (x := 0) (by omega))
    (fun h => RunZ.lit0.eq ?_) (fun h => hmul.eq ?_))) ?_
  · have hnot : ¬ validIdx cheap m ξ := by
      intro hv
      simp [hv] at h
    rw [rectA, hcheap, if_neg hnot]
  · have hv : validIdx cheap m ξ := by
      by_contra hv
      simp [hv] at h
    rw [rectA, hcheap, if_pos hv]
    push_cast
    rfl
  · unfold rectCost rectCoefCost cntCost coefCCost coefRCost fpatCost validCost letterCost
    nlinarith

open Rect in
/-- **The second factor.** -/
theorem runZ_rectBE {W sc bk : ℕ} (hB : RectBig W sc bk) {env : List ℕ}
    {id ipol im ixi ir is : ℕ} {dir pol : Bool} {m ξ r s : ℕ}
    (hd : env.getD id 0 = dir.toNat) (hpol : env.getD ipol 0 = pol.toNat)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) (hr : env.getD ir 0 = r) (hs : env.getD is 0 = s)
    (hmsc : m ≤ sc) (hξ : ξ < 2 ^ (2 * sc)) :
    RunZ W (rectBE id ipol im ixi ir is) env (rectB dir pol m ξ r s) (rectCost sc) := by
  have hW := hB.hW
  have hC := run_cheap (W := W) (env := env) (by omega) hpol hd
  generalize hcheap : (pol == dir) = cheap at hC
  have hc0 : (cheap.toNat :: env).getD 0 0 = cheap.toNat := rfl
  have hV := run_validE (W := W) (env := cheap.toNat :: env) (im := im + 1) (ixi := ixi + 1) hW hmsc hξ
    hc0 (up hm) (up hx)
  have hfpat := runZ_fpatE (env := cheap.toNat :: env) (id := id + 1) (im := im + 1) (ixi := ixi + 1)
    (ip := ir + 1) (iq := is + 1) hW hmsc hc0 (up hd) (up hm) (up hx) (up hr) (up hs)
  refine RunZ.mono (RunZ.letE hC (RunZ.ite hV (run_lit (x := 0) (by omega))
    (fun h => RunZ.lit0.eq ?_) (fun h => hfpat.eq ?_))) ?_
  · have hnot : ¬ validIdx cheap m ξ := by
      intro hv
      simp [hv] at h
    rw [rectB, hcheap, if_neg hnot]
  · have hv : validIdx cheap m ξ := by
      by_contra hv
      simp [hv] at h
    rw [rectB, hcheap, if_pos hv]
  · unfold rectCost fpatCost validCost letterCost
    nlinarith

end UncrossingWires.Pseudo
