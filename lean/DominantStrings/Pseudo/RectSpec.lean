import DominantStrings.Pseudo.Frame

/-!
# The programs of the two factors of a rectangle

Each helper of `DominantStrings/Pseudo/Prog.lean` gets one statement `Run` (an exact value) or `RunZ` (a value in the ring of
words), with a cost that is an explicit function of the scale `sc`. A Boolean is held as `b.toNat` in a variable.
-/

namespace DominantStrings.Pseudo

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

/-! ### `admBE`, `markE` -/

/-- The operations of `admBE`. -/
def admCost (sc : ℕ) : ℕ := 40 + 7 * sc

theorem run_admBE {im iM m M : ℕ} (hW : 8 * sc + 8 < W) (hmsc : m ≤ sc) (hm1 : 1 ≤ m)
    (hm : env.getD im 0 = m) (hM : env.getD iM 0 = M) :
    Run W (admBE im iM) env (if admB m M then 1 else 0) (admCost sc) := by
  have hmW : m < W := by omega
  have hp := run_popBE (W := W) (env := env) (T := sc) (by omega) hmW hmsc hM hm
  generalize hpdef : popB M m = p at hp
  have hpm : p ≤ m := hpdef ▸ popB_le M m
  have h2p : Run W (.mul (.lit 2) (.var 0)) (p :: env) (2 * p) 3 :=
    Run.mono (Run.mul (run_lit (x := 2) (by omega)) (Run.var rfl) (small_lt (by omega))) (by omega)
  have hmv : Run W (.var (im + 1)) (p :: env) m 1 := Run.var (up hm)
  have hbit : Run W (bitX (iM + 1) (.sub (.var (im + 1)) (.lit 1))) (p :: env) (M.testBit (m - 1)).toNat 8 :=
    Run.mono (Run.bitX (up hM) (Run.sub (Run.var (up hm)) (run_lit (x := 1) (by omega)) (small_lt hmW) hm1)
      (by omega) (by omega)) (by omega)
  refine Run.mono (Run.letE hp (Run.ite h2p hmv
    (fun h1 => Run.ite hmv h2p (fun h2 => hbit.eq ?_) (fun h2 => (run_lit (x := 0) (by omega)).eq ?_))
    (fun h1 => (run_lit (x := 1) (by omega)).eq ?_))) ?_
  · have he : 2 * p = m := by omega
    by_cases hb : M.testBit (m - 1) = true
    · have : admB m M := Or.inr ⟨by rw [hpdef, he], hb⟩
      rw [if_pos this, hb]
      rfl
    · have : ¬ admB m M := by
        rintro (h | ⟨_, h⟩)
        · rw [hpdef] at h
          omega
        · exact hb h
      have hb' : M.testBit (m - 1) = false := by simpa using hb
      rw [if_neg this, hb']
      rfl
  · have : ¬ admB m M := by
      rintro (h | ⟨h, _⟩) <;> rw [hpdef] at h <;> omega
    rw [if_neg this]
  · have : admB m M := Or.inl (by rw [hpdef]; omega)
    rw [if_pos this]
  · unfold admCost
    omega

/-- The operations of `markE`. -/
def markCost (sc : ℕ) : ℕ := 70 + 7 * sc

theorem run_markE {im ixi m ξ : ℕ} (hW : 8 * sc + 8 < W) (hmsc : m ≤ sc) (hm1 : 1 ≤ m)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) :
    Run W (markE im ixi) env (markOf m ξ) (markCost sc) := by
  have hmW : m < W := by omega
  have hsub : Run W (.sub (.var im) (.lit 1)) env (m - 1) 3 :=
    Run.mono (Run.sub (Run.var hm) (run_lit (x := 1) (by omega)) (small_lt hmW) hm1) (by omega)
  have hp := Run.pow2 hsub (by omega : m - 1 < W)
  have hlow : ξ % 2 ^ (m - 1) < 2 ^ (m - 1) := Nat.mod_lt _ (by positivity)
  have hm2 : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  have hmWp : 2 ^ m < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hmW
  have hB := Run.add (Run.mod (Run.var hx) hp) hp (by omega)
  have hBlt : ξ % 2 ^ (m - 1) + 2 ^ (m - 1) < 2 ^ m := by omega
  generalize hBdef : ξ % 2 ^ (m - 1) + 2 ^ (m - 1) = B at hB hBlt
  have hA := run_admBE (W := W) (env := B :: env) (im := im + 1) (iM := 0) hW hmsc hm1 (up hm) rfl
  have hc : Run W (.sub (.sub (.pow2 (.var (im + 1))) (.lit 1)) (.var 0)) (B :: env) (2 ^ m - 1 - B) 7 := by
    have h1 := Run.pow2 (Run.var (W := W) (env := B :: env) (up hm)) hmW
    have h2 := Run.sub h1 (run_lit (x := 1) (by omega)) hmWp Nat.one_le_two_pow
    exact Run.mono (Run.sub h2 (Run.var rfl) (by omega) (by omega)) (by omega)
  have hmk : markOf m ξ = if admB m B then B else 2 ^ m - 1 - B := by
    simp only [markOf, hBdef]
  refine Run.mono (Run.letE hB (Run.ite (run_lit (x := 1) (by omega)) hA
    (fun h => (Run.var rfl).eq ?_) (fun h => hc.eq ?_))) ?_
  · have : admB m B := by
      by_contra hn
      simp [hn] at h
    rw [hmk, if_pos this]
    rfl
  · have : ¬ admB m B := by
      intro hn
      simp [hn] at h
    rw [hmk, if_neg this]
  · unfold markCost admCost at *
    omega

/-! ### `letterE` -/

/-- The operations of `letterE`. -/
def letterCost (sc : ℕ) : ℕ := 150 + 16 * sc

theorem run_letterE {ic id im ixi ij : ℕ} {cheap : Bool} {m ξ j : ℕ} (hW : 8 * sc + 8 < W)
    (hmsc : m ≤ sc) (hc : env.getD ic 0 = cheap.toNat)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) (hj : env.getD ij 0 = j) :
    Run W (letterE ic id im ixi ij) env (letterOf cheap m ξ j) (letterCost sc) := by
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
  have hcheap : j < m → Run W (.letE (markE im ixi) <|
        .ite (bitX 0 (.var (ij + 1))) (.lit 0)
          (.mod (.div (.div (.var (ixi + 1)) (.pow2 (.sub (.var (im + 1)) (.lit 1))))
            (pow3E (.sub (.var (ij + 1)) (popBE 0 (ij + 1))))) (.lit 3))
          (.lit 3)) env (letterCheap m ξ j)
      (120 + 16 * sc) := by
    intro hjm
    have hjW : j < W := by omega
    have hsc1 : j ≤ sc := by omega
    have hM := run_markE (W := W) (env := env) hW hmsc (by omega) hm hx
    generalize hMdef : markOf m ξ = M at hM
    have hsub : Run W (.sub (.var (ij + 1)) (popBE 0 (ij + 1))) (M :: env) (j - popB M j)
        (1 + 1 + (2 + sc * 7)) :=
      Run.sub (Run.var hj) (run_popBE (T := sc) (by omega) hjW hsc1 rfl hj) (small_lt hjW) (popB_le M j)
    have hk : j - popB M j ≤ sc := by omega
    have hpow := run_pow3E (T := sc) (by omega) hsub hk (three_pow_lt (by omega))
    have hsm : Run W (.sub (.var (im + 1)) (.lit 1)) (M :: env) (m - 1) 3 :=
      Run.mono (Run.sub (Run.var (up hm)) (run_lit (x := 1) (by omega)) (small_lt hmW) (by omega)) (by omega)
    have hdig := Run.mod (Run.div (Run.div (Run.var (W := W) (up (x := M) hx))
      (Run.pow2 hsm (by omega : m - 1 < W))) hpow) (run_lit (x := 3) (by omega))
    refine Run.mono (Run.letE hM (Run.ite (Run.bitX rfl (Run.var hj) hjW (by omega))
      (run_lit (x := 0) (by omega)) (fun h => hdig.eq ?_) (fun h => (run_lit (x := 3) (by omega)).eq ?_))) ?_
    · have hb : M.testBit j = false := by cases hbit : M.testBit j <;> simp_all
      rw [letterCheap, hMdef, hb]
      simp
    · have hb : M.testBit j = true := by cases hbit : M.testBit j <;> simp_all
      rw [letterCheap, hMdef, hb]
      simp
    · unfold markCost
      omega
  refine Run.mono (Run.ite (Run.var hm) (Run.var hj) (r := letterOf cheap m ξ j)
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

theorem b2z_toNat (A : Bool) : ((A.toNat : ℕ) : ℤ) = b2z A := by cases A <;> rfl

theorem runZ_topE {il l ca cb : ℕ} {a b : Expr} {A B : Bool} (hW : 4 ≤ W)
    (hl : env.getD il 0 = l) (ha : Run W a env A.toNat ca) (hb : Run W b env B.toNat cb) :
    RunZ W (topE il a b) env (topL l A B) (20 + 4 * (ca + cb)) := by
  have e0 : RunZ W (.mul a b) env (b2z A * b2z B) (1 + ca + cb) :=
    (RunZ.mul ha.toZ hb.toZ).eq (by rw [b2z_toNat, b2z_toNat])
  have e2 : RunZ W (.add a b) env (b2z A + b2z B) (1 + ca + cb) :=
    (RunZ.add ha.toZ hb.toZ).eq (by rw [b2z_toNat, b2z_toNat])
  have e3 : RunZ W (.sub a b) env (b2z A - b2z B) (1 + ca + cb) :=
    (RunZ.sub ha.toZ hb.toZ).eq (by rw [b2z_toNat, b2z_toNat])
  refine RunZ.mono (RunZ.ite (Run.var hl) (run_lit (x := 0) (by omega)) (fun h0 => e0.eq ?_)
    (fun h0 => RunZ.ite (Run.var hl) (run_lit (x := 1) (by omega)) (fun h1 => RunZ.lit1.eq ?_)
      (fun h1 => RunZ.ite (Run.var hl) (run_lit (x := 2) (by omega)) (fun h2 => e2.eq ?_)
        (fun h2 => e3.eq ?_)))) (by omega)
  · obtain rfl : l = 0 := by omega
    rfl
  · obtain rfl : l = 1 := by omega
    rfl
  · obtain rfl : l = 2 := by omega
    rfl
  · obtain ⟨n, rfl⟩ : ∃ n, l = n + 3 := ⟨l - 3, by omega⟩
    rfl

theorem runZ_botE {il l ca cb : ℕ} {a b : Expr} {A B : Bool} (hW : 4 ≤ W)
    (hl : env.getD il 0 = l) (ha : Run W a env A.toNat ca) (hb : Run W b env B.toNat cb) :
    RunZ W (botE il a b) env (botL l A B) (20 + 4 * (ca + cb)) := by
  have e1 : RunZ W (.mul a b) env (b2z A * b2z B) (1 + ca + cb) :=
    (RunZ.mul ha.toZ hb.toZ).eq (by rw [b2z_toNat, b2z_toNat])
  have e2 : RunZ W (.add a b) env (b2z A + b2z B) (1 + ca + cb) :=
    (RunZ.add ha.toZ hb.toZ).eq (by rw [b2z_toNat, b2z_toNat])
  have e3 : RunZ W (.sub a b) env (b2z A - b2z B) (1 + ca + cb) :=
    (RunZ.sub ha.toZ hb.toZ).eq (by rw [b2z_toNat, b2z_toNat])
  refine RunZ.mono (RunZ.ite (Run.var hl) (run_lit (x := 0) (by omega)) (fun h0 => RunZ.lit1.eq ?_)
    (fun h0 => RunZ.ite (Run.var hl) (run_lit (x := 1) (by omega)) (fun h1 => e1.eq ?_)
      (fun h1 => RunZ.ite (Run.var hl) (run_lit (x := 2) (by omega)) (fun h2 => e2.eq ?_)
        (fun h2 => e3.eq ?_)))) (by omega)
  · obtain rfl : l = 0 := by omega
    rfl
  · obtain rfl : l = 1 := by omega
    rfl
  · obtain rfl : l = 2 := by omega
    rfl
  · obtain ⟨n, rfl⟩ : ∃ n, l = n + 3 := ⟨l - 3, by omega⟩
    rfl

/-- The operations of `fpatTE` and `fpatBE`. -/
def fpatCost (sc : ℕ) : ℕ := 2 + sc * (175 + letterCost sc)

theorem runZ_fpatTE {ic id im ixi ip iq : ℕ} {cheap : Bool} {m ξ p q : ℕ} (hW : 8 * sc + 8 < W)
    (hmsc : m ≤ sc) (hc : env.getD ic 0 = cheap.toNat)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) (hp : env.getD ip 0 = p)
    (hq : env.getD iq 0 = q) :
    RunZ W (fpatTE ic id im ixi ip iq) env (fpatT m (letterOf cheap m ξ) p q) (fpatCost sc) := by
  have hbody : ∀ j < m, RunZ W (.letE (letterE (ic + 1) (id + 1) (im + 1) (ixi + 1) 0) <|
      topE 0 (bitX (ip + 2) (.var 1)) (bitX (iq + 2) (.var 1))) (j :: env)
      (topL (letterOf cheap m ξ j) (p.testBit j) (q.testBit j)) (1 + letterCost sc + 173) := by
    intro j hj
    have hL := run_letterE (W := W) (id := id + 1) (ij := 0) (j := j) (env := j :: env) hW hmsc (up hc) (up hm)
      (up hx) rfl
    have hbp := Run.bitX (W := W) (env := letterOf cheap m ξ j :: j :: env) (up (up hp))
      (Run.var (up (x := letterOf cheap m ξ j) (i := 0) (v := j) rfl)) (by omega) (by omega)
    have hbq := Run.bitX (W := W) (env := letterOf cheap m ξ j :: j :: env) (up (up hq))
      (Run.var (up (x := letterOf cheap m ξ j) (i := 0) (v := j) rfl)) (by omega) (by omega)
    exact RunZ.mono (RunZ.letE hL (runZ_topE (by omega) rfl hbp hbq)) (by omega)
  refine RunZ.mono (RunZ.prod (Run.var hm) hmsc hbody) ?_
  unfold fpatCost
  have : sc * (1 + letterCost sc + 173 + 1) = sc * (175 + letterCost sc) := by ring
  omega

theorem runZ_fpatBE {ic id im ixi ip iq : ℕ} {cheap : Bool} {m ξ p q : ℕ} (hW : 8 * sc + 8 < W)
    (hmsc : m ≤ sc) (hc : env.getD ic 0 = cheap.toNat)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ) (hp : env.getD ip 0 = p)
    (hq : env.getD iq 0 = q) :
    RunZ W (fpatBE ic id im ixi ip iq) env (fpatB m (letterOf cheap m ξ) p q) (fpatCost sc) := by
  have hbody : ∀ j < m, RunZ W (.letE (letterE (ic + 1) (id + 1) (im + 1) (ixi + 1) 0) <|
      botE 0 (bitX (ip + 2) (.var 1)) (bitX (iq + 2) (.var 1))) (j :: env)
      (botL (letterOf cheap m ξ j) (p.testBit j) (q.testBit j)) (1 + letterCost sc + 173) := by
    intro j hj
    have hL := run_letterE (W := W) (id := id + 1) (ij := 0) (j := j) (env := j :: env) hW hmsc (up hc) (up hm)
      (up hx) rfl
    have hbp := Run.bitX (W := W) (env := letterOf cheap m ξ j :: j :: env) (up (up hp))
      (Run.var (up (x := letterOf cheap m ξ j) (i := 0) (v := j) rfl)) (by omega) (by omega)
    have hbq := Run.bitX (W := W) (env := letterOf cheap m ξ j :: j :: env) (up (up hq))
      (Run.var (up (x := letterOf cheap m ξ j) (i := 0) (v := j) rfl)) (by omega) (by omega)
    exact RunZ.mono (RunZ.letE hL (runZ_botE (by omega) rfl hbp hbq)) (by omega)
  refine RunZ.mono (RunZ.prod (Run.var hm) hmsc hbody) ?_
  unfold fpatCost
  have : sc * (1 + letterCost sc + 173 + 1) = sc * (175 + letterCost sc) := by ring
  omega

/-- The operations of `cntE`. -/
def cntCost (sc : ℕ) : ℕ := 2 + sc * (12 + letterCost sc)

theorem run_cntE {ic id im ixi ik l : ℕ} {cheap : Bool} {m ξ k : ℕ} (hW : 8 * sc + 8 < W)
    (hmsc : m ≤ sc) (hkm : k ≤ m) (hl : l < W) (hc : env.getD ic 0 = cheap.toNat)
    (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ)
    (hk : env.getD ik 0 = k) :
    Run W (cntE ic id im ixi ik l) env (cnt k (letterOf cheap m ξ) l) (cntCost sc) := by
  have hbody : ∀ j < k, Run W (.letE (letterE (ic + 1) (id + 1) (im + 1) (ixi + 1) 0) <|
      eqX (.var 0) (.lit l) (.lit 1) (.lit 0)) (j :: env)
      (if letterOf cheap m ξ j = l then 1 else 0) (1 + letterCost sc + 10) := by
    intro j hj
    have hL := run_letterE (W := W) (id := id + 1) (ij := 0) (j := j) (env := j :: env) hW hmsc (up hc) (up hm)
      (up hx) rfl
    refine Run.mono (Run.letE hL (Run.eqX (Run.var rfl) (run_lit hl)
      (fun h => (run_lit (x := 1) (by omega)).eq (if_pos h).symm)
      (fun h => (run_lit (x := 0) (by omega)).eq (if_neg h).symm))) (by omega)
  have hlt : ∑ j ∈ range k, (if letterOf cheap m ξ j = l then 1 else 0) < 2 ^ W :=
    lt_of_le_of_lt (cnt_le k _ l) (small_lt (by omega))
  refine Run.mono (Run.sum (Run.var hk) (by omega : k ≤ sc) hbody hlt) ?_
  unfold cntCost
  have : sc * (1 + letterCost sc + 10 + 1) = sc * (12 + letterCost sc) := by ring
  omega

/-! ### `condTE`, `signE`, the binomials -/

theorem runZ_condTE {ipol it ir t r cc cd : ℕ} {pol : Bool} {c d : Expr} {u v : ℤ} (hW : 4 ≤ W)
    (hpol : env.getD ipol 0 = pol.toNat) (ht : env.getD it 0 = t)
    (hr : env.getD ir 0 = r) (hc : RunZ W c env u cc) (hd : RunZ W d env v cd) :
    RunZ W (condTE ipol it ir c d) env (if condT pol t r then u else v) (9 + 2 * (cc + cd)) := by
  have h1 : RunZ W (.ite (.var it) (.var ir) d c) env (if r < t then u else v) (1 + 1 + 1 + (cd + cc)) :=
    RunZ.ite (Run.var ht) (Run.var hr) (fun h => hd.eq (if_neg (by omega)).symm)
      (fun h => hc.eq (if_pos (by omega)).symm)
  have h2 : RunZ W (.ite (.var it) (.var ir) c d) env (if t ≤ r then u else v) (1 + 1 + 1 + (cc + cd)) :=
    RunZ.ite (Run.var ht) (Run.var hr) (fun h => hc.eq (if_pos h).symm) (fun h => hd.eq (if_neg h).symm)
  refine RunZ.mono (RunZ.ite (Run.var hpol) (run_lit (x := 0) (by omega))
    (fun h => h1.eq ?_) (fun h => h2.eq ?_)) (by omega)
  · have : pol = false := by cases pol <;> simp_all
    subst this
    simp [condT]
  · have : pol = true := by cases pol <;> simp_all
    subst this
    simp [condT]

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

/-- The operations of `coefRtE`. -/
def coefRCost (sc : ℕ) : ℕ := 4 + (sc + 1) * (66 + 10 * sc)

theorem runZ_coefRtE {ipol it in3 ibk t n3 : ℕ} {pol : Bool} (hB : RectBig W sc bk)
    (hpol : env.getD ipol 0 = pol.toNat) (ht : env.getD it 0 = t) (hn3 : env.getD in3 0 = n3)
    (hbk : env.getD ibk 0 = bk) (hn3sc : n3 ≤ sc) :
    RunZ W (coefRtE ipol it in3 ibk) env (coefRt pol t n3) (coefRCost sc) := by
  have hW := hB.hW
  have hS : Lag.Sizes W n3 bk := sizes_mono hB.sizes hn3sc
  have hbody : ∀ r < n3 + 1, RunZ W (condTE (ipol + 1) (it + 1) 0
      (.mul (.mul (Lag.chooseE (in3 + 1) (ibk + 1) 0) (signE 0)) (.pow2 (.var 0))) (.lit 0)) (r :: env)
      (if condT pol t r then (n3.choose r : ℤ) * (-2) ^ r else 0) (65 + 10 * sc) := by
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
    refine RunZ.mono (runZ_condTE (r := r) (by omega) (up hpol) (up ht) rfl hc' RunZ.lit0)
      (by omega)
  refine RunZ.mono (RunZ.sum (T := sc + 1)
    (Run.add (Run.var hn3) (run_lit (x := 1) (by omega)) (small_lt (by omega))) (by omega) hbody) ?_
  unfold coefRCost
  have : (sc + 1) * (65 + 10 * sc + 1) = (sc + 1) * (66 + 10 * sc) := by ring
  omega

/-- The operations of `coefCtE`. -/
def coefCCost (sc : ℕ) : ℕ := 14 + (sc + 1) * (76 + 10 * sc)

theorem runZ_coefCtE {ipol it ik in3 ibk t k n3 : ℕ} {pol : Bool} (hB : RectBig W sc bk)
    (hpol : env.getD ipol 0 = pol.toNat) (ht : env.getD it 0 = t) (hk : env.getD ik 0 = k)
    (hn3 : env.getD in3 0 = n3) (hbk : env.getD ibk 0 = bk) (hksc : k ≤ sc) (hn3k : n3 ≤ k) :
    RunZ W (coefCtE ipol it ik in3 ibk) env (coefCt pol t k n3) (coefCCost sc) := by
  have hW := hB.hW
  have hS : Lag.Sizes W n3 bk := sizes_mono hB.sizes (by omega)
  have hbody : ∀ r < n3 + 1, RunZ W (.letE (.add (.sub (.var (ik + 1)) (.var (in3 + 1))) (.var 0)) <|
        condTE (ipol + 2) (it + 2) 0
          (.mul (.mul (Lag.chooseE (in3 + 2) (ibk + 2) 1) (.pow2 (.sub (.var (in3 + 2)) (.var 1))))
            (signE 1)) (.lit 0)) (r :: env)
      (if condT pol t (k - n3 + r) then (n3.choose r : ℤ) * 2 ^ (n3 - r) * (-1) ^ r else 0)
      (75 + 10 * sc) := by
    intro r hr
    have hx : Run W (.add (.sub (.var (ik + 1)) (.var (in3 + 1))) (.var 0)) (r :: env) (k - n3 + r)
        5 := Run.mono (Run.add (Run.sub (Run.var (up hk)) (Run.var (up hn3))
          (small_lt (by omega)) hn3k) (Run.var rfl) (small_lt (by omega))) (by omega)
    have hr0 : ((k - n3 + r) :: r :: env).getD 1 0 = r := rfl
    have hc := RunZ.mul (RunZ.mul (run_chooseE (env := (k - n3 + r) :: r :: env) (r := r) hS
      (up (up hn3)) (up (up hbk)) hr0 (by omega)).toZ
      (Run.pow2 (Run.sub (Run.var (up (up hn3))) (Run.var hr0) (small_lt (by omega)) (by omega))
        (by omega)).toZ)
      (runZ_signE (r := r) (by omega) hr0)
    have hc' : RunZ W (.mul (.mul (Lag.chooseE (in3 + 2) (ibk + 2) 1)
        (.pow2 (.sub (.var (in3 + 2)) (.var 1)))) (signE 1)) ((k - n3 + r) :: r :: env)
        ((n3.choose r : ℤ) * 2 ^ (n3 - r) * (-1) ^ r) (25 + 5 * n3) := by
      refine RunZ.mono (hc.eq ?_) (by omega)
      push_cast
      ring
    exact RunZ.mono (RunZ.letE hx (runZ_condTE (r := k - n3 + r) (by omega) (up (up hpol))
      (up (up ht)) rfl hc' RunZ.lit0)) (by omega)
  refine RunZ.mono (RunZ.sum (T := sc + 1)
    (Run.add (Run.var hn3) (run_lit (x := 1) (by omega)) (small_lt (by omega))) (by omega) hbody) ?_
  unfold coefCCost
  have : (sc + 1) * (75 + 10 * sc + 1) = (sc + 1) * (76 + 10 * sc) := by ring
  omega

/-- The operations of `rectCoefE`. -/
def rectCoefCost (sc : ℕ) : ℕ := 300 + 4 * cntCost sc + letterCost sc + 2 * (coefCCost sc + coefRCost sc)

/-- A small integer constant, as `c` or `0 - c`. -/
theorem runZ_negLit {c : ℕ} (hW : 4 ≤ W) (hc : c < 4) :
    RunZ W (.sub (.lit 0) (.lit c)) env (-(c : ℤ)) 3 :=
  (RunZ.sub RunZ.lit0 (RunZ.lit c)).eq (by ring)

set_option maxHeartbeats 2000000 in
theorem runZ_rectCoefE {ic id ipol im ixi ibk m ξ : ℕ} {cheap dir pol : Bool} (hB : RectBig W sc bk)
    (hc : env.getD ic 0 = cheap.toNat) (hd : env.getD id 0 = dir.toNat)
    (hpol : env.getD ipol 0 = pol.toNat) (hm : env.getD im 0 = m) (hx : env.getD ixi 0 = ξ)
    (hbk : env.getD ibk 0 = bk) (hmsc : m ≤ sc) :
    RunZ W (rectCoefE ic id ipol im ixi ibk) env (rectCoef dir pol m (letterOf cheap m ξ))
      (rectCoefCost sc) := by
  unfold rectCoefE
  have hW := hB.hW
  have hzero : RunZ W (.ite (.var ipol) (.lit 0) (.lit 1) (.lit 0)) env (if pol then 0 else 1) 5 := by
    refine RunZ.mono (RunZ.ite (Run.var hpol) (run_lit (x := 0) (by omega))
      (fun h => RunZ.lit1.eq ?_) (fun h => RunZ.lit0.eq ?_)) (by omega)
    · cases pol <;> simp_all
    · cases pol <;> simp_all
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    refine RunZ.mono (RunZ.ite (cd := 0) (Run.var hm) (run_lit (x := 0) (by omega))
      (fun _ => hzero.eq ?_) (fun h => absurd (le_refl 0) h)) ?_
    · simp [rectCoef]
    · unfold rectCoefCost
      omega
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : Run W (.sub (.var im) (.lit 1)) env k 3 :=
    Run.mono ((Run.sub (Run.var hm) (run_lit (x := 1) (by omega)) (small_lt (by omega)) (by omega)).eq
      (by omega)) (by omega)
  have h3 := run_cntE (env := k :: env) (k := k) (ic := ic + 1) (id := id + 1) (im := im + 1) (ixi := ixi + 1)
    (ik := 0) (l := 3) hW hmsc (by omega) (by omega) (up hc) (up hm) (up hx) rfl
  generalize hn3 : cnt k (letterOf cheap (k + 1) ξ) 3 = n3 at h3
  have h0 := run_cntE (env := n3 :: k :: env) (k := k) (ic := ic + 2) (id := id + 2) (im := im + 2)
    (ixi := ixi + 2) (ik := 1) (l := 0) hW hmsc (by omega) (by omega) (up (up hc)) (up (up hm))
    (up (up hx)) rfl
  generalize hn0 : cnt k (letterOf cheap (k + 1) ξ) 0 = n0 at h0
  have h1 := run_cntE (env := n0 :: n3 :: k :: env) (k := k) (ic := ic + 3) (id := id + 3) (im := im + 3)
    (ixi := ixi + 3) (ik := 2) (l := 1) hW hmsc (by omega) (by omega) (up (up (up hc))) (up (up (up hm)))
    (up (up (up hx))) rfl
  generalize hn1 : cnt k (letterOf cheap (k + 1) ξ) 1 = n1 at h1
  have h2 := run_cntE (env := n1 :: n0 :: n3 :: k :: env) (k := k) (ic := ic + 4) (id := id + 4)
    (im := im + 4) (ixi := ixi + 4) (ik := 3) (l := 2) hW hmsc (by omega) (by omega) (up (up (up (up hc))))
    (up (up (up (up hm)))) (up (up (up (up hx)))) rfl
  generalize hn2 : cnt k (letterOf cheap (k + 1) ξ) 2 = n2 at h2
  have hn3k : n3 ≤ k := hn3 ▸ cnt_le _ _ _
  have hn0k : n0 ≤ k := hn0 ▸ cnt_le _ _ _
  have hn1k : n1 ≤ k := hn1 ▸ cnt_le _ _ _
  have htp := run_letterE (env := n2 :: n1 :: n0 :: n3 :: k :: env) (ic := ic + 5) (id := id + 5)
    (im := im + 5) (ixi := ixi + 5) (ij := 4) (j := k) hW hmsc (up (up (up (up (up hc)))))
    (up (up (up (up (up hm))))) (up (up (up (up (up hx))))) rfl
  generalize htpd : letterOf cheap (k + 1) ξ k = tp at htp
  have htp4 : tp < 4 := by
    rw [← htpd]
    simp only [letterOf, Nat.lt_succ_self, if_true]
    split_ifs
    · simp only [letterCheap]
      split_ifs <;> omega
    · simp only [letterPlain]
      omega
  have ht0 : Run W (.div (.add (.var 5) (.lit 3)) (.lit 2)) (tp :: n2 :: n1 :: n0 :: n3 :: k :: env)
      (thr0 k) 5 :=
    Run.mono (Run.div (Run.add (Run.var rfl) (run_lit (x := 3) (by omega)) (small_lt (by omega)))
      (run_lit (x := 2) (by omega))) (by omega)
  have ht1 : Run W (.div (.var 6) (.lit 2)) (thr0 k :: tp :: n2 :: n1 :: n0 :: n3 :: k :: env) (thr1 k) 3 :=
    Run.mono (Run.div (Run.var rfl) (run_lit (x := 2) (by omega))) (by omega)
  have hP2 : Run W (.pow2 (.add (.var 5) (.var 4))) (thr1 k :: thr0 k :: tp :: n2 :: n1 :: n0 :: n3 :: k :: env)
      (2 ^ (n0 + n1)) 4 :=
    Run.mono (Run.pow2 (Run.add (Run.var rfl) (Run.var rfl) (small_lt (by omega))) (by omega)) (by omega)
  set E := 2 ^ (n0 + n1) :: thr1 k :: thr0 k :: tp :: n2 :: n1 :: n0 :: n3 :: k :: env with hE
  have eP2 : E.getD 0 0 = 2 ^ (n0 + n1) := rfl
  have eT1 : E.getD 1 0 = thr1 k := rfl
  have eT0 : E.getD 2 0 = thr0 k := rfl
  have eTp : E.getD 3 0 = tp := rfl
  have eN2 : E.getD 4 0 = n2 := rfl
  have eN1 : E.getD 5 0 = n1 := rfl
  have eN0 : E.getD 6 0 = n0 := rfl
  have eN3 : E.getD 7 0 = n3 := rfl
  have eK : E.getD 8 0 = k := rfl
  have hpolE : E.getD (ipol + 9) 0 = pol.toNat := hpol
  have hbkE : E.getD (ibk + 9) 0 = bk := hbk
  have hdE : E.getD (id + 9) 0 = dir.toNat := hd
  have hC0 := runZ_coefCtE (env := E) (t := thr0 k) (k := k) (n3 := n3) (ipol := ipol + 9) (it := 2) (ik := 8)
    (in3 := 7) (ibk := ibk + 9) hB hpolE eT0 eK eN3 hbkE (by omega) hn3k
  have hC1 := runZ_coefCtE (env := E) (t := thr1 k) (k := k) (n3 := n3) (ipol := ipol + 9) (it := 1) (ik := 8)
    (in3 := 7) (ibk := ibk + 9) hB hpolE eT1 eK eN3 hbkE (by omega) hn3k
  have hR0 := runZ_coefRtE (env := E) (t := thr0 k) (n3 := n3) (ipol := ipol + 9) (it := 2) (in3 := 7)
    (ibk := ibk + 9) hB hpolE eT0 eN3 hbkE (by omega)
  have hR1 := runZ_coefRtE (env := E) (t := thr1 k) (n3 := n3) (ipol := ipol + 9) (it := 1) (in3 := 7)
    (ibk := ibk + 9) hB hpolE eT1 eN3 hbkE (by omega)
  have hbC : RunZ W (eqX (.var 3) (.lit 3) (.lit 2) (.lit 0)) E (bC tp) 10 :=
    RunZ.mono (RunZ.eqX (Run.var eTp) (run_lit (x := 3) (by omega))
      (fun h => (RunZ.lit 2).eq (by rw [bC, if_pos h]; norm_num)) (fun h => RunZ.lit0.eq (by rw [bC, if_neg h])))
      (by omega)
  have haC : RunZ W (.ite (.var 3) (.lit 1) (.sub (.lit 0) (.lit 2))
      (eqX (.var 3) (.lit 2) (.lit 1) (.sub (.lit 0) (.lit 1)))) E (aC tp) 24 := by
    refine RunZ.mono (RunZ.ite (Run.var eTp) (run_lit (x := 1) (by omega))
      (fun h => (runZ_negLit (c := 2) (by omega) (by omega)).eq ?_)
      (fun h => RunZ.eqX (Run.var eTp) (run_lit (x := 2) (by omega)) (fun h2 => RunZ.lit1.eq ?_)
        (fun h2 => (runZ_negLit (c := 1) (by omega) (by omega)).eq ?_))) (by omega)
    · rw [aC, if_pos (by omega)]
      norm_num
    · rw [aC, if_neg (by omega), if_pos h2]
    · rw [aC, if_neg (by omega), if_neg h2]
      norm_num
  have hbR : RunZ W (.ite (.var 3) (.lit 1) (.lit 2) (eqX (.var 3) (.lit 2) (.sub (.lit 0) (.lit 1)) (.lit 1)))
      E (bR tp) 24 := by
    refine RunZ.mono (RunZ.ite (Run.var eTp) (run_lit (x := 1) (by omega))
      (fun h => (RunZ.lit 2).eq ?_)
      (fun h => RunZ.eqX (Run.var eTp) (run_lit (x := 2) (by omega))
        (fun h2 => (runZ_negLit (c := 1) (by omega) (by omega)).eq ?_) (fun h2 => RunZ.lit1.eq ?_))) (by omega)
    · rw [bR, if_pos (by omega)]
      norm_num
    · rw [bR, if_neg (by omega), if_pos h2]
      norm_num
    · rw [bR, if_neg (by omega), if_neg h2]
  have haR : RunZ W (eqX (.var 3) (.lit 3) (.sub (.lit 0) (.lit 2)) (.lit 0)) E (aR tp) 14 :=
    RunZ.mono (RunZ.eqX (Run.var eTp) (run_lit (x := 3) (by omega))
      (fun h => (runZ_negLit (c := 2) (by omega) (by omega)).eq (by rw [aR, if_pos h]; norm_num))
      (fun h => RunZ.lit0.eq (by rw [aR, if_neg h]))) (by omega)
  have hsg01 : RunZ W (.ite (.mod (.add (.var 6) (.var 5)) (.lit 2)) (.lit 0) (.lit 1) (.sub (.lit 0) (.lit 1)))
      E ((-1) ^ (n0 + n1)) 12 := by
    refine RunZ.mono (RunZ.ite (Run.mod (Run.add (Run.var eN0) (Run.var eN1) (small_lt (by omega)))
      (run_lit (x := 2) (by omega))) (run_lit (x := 0) (by omega)) (fun h => RunZ.lit1.eq ?_)
      (fun h => (RunZ.sub RunZ.lit0 RunZ.lit1).eq ?_)) (by omega)
    · have : Even (n0 + n1) := Nat.even_iff.mpr (by omega)
      rw [this.neg_one_pow]
    · have : Odd (n0 + n1) := Nat.odd_iff.mpr (by omega)
      rw [this.neg_one_pow]
      norm_num
  have hcols := RunZ.mul (RunZ.add (RunZ.mul hbC hC0) (RunZ.mul haC hC1)) (RunZ.mul hsg01 (Run.var eP2).toZ)
  have hrows := RunZ.mul (RunZ.add (RunZ.mul hbR hR0) (RunZ.mul haR hR1))
    (RunZ.mul (Run.var eP2).toZ (runZ_signE (by omega) eN2))
  refine RunZ.mono (RunZ.ite (cc := 0) (Run.var hm) (run_lit (x := 0) (by omega))
    (fun h => absurd h (by omega))
    (fun _ => RunZ.letE hk (RunZ.letE h3 (RunZ.letE h0 (RunZ.letE h1 (RunZ.letE h2 (RunZ.letE htp
      (RunZ.letE ht0 (RunZ.letE ht1 (RunZ.letE hP2
      (RunZ.ite (Run.var hdE) (run_lit (x := 0) (by omega))
        (fun h => hcols.eq ?_) (fun h => hrows.eq ?_)))))))))))) ?_
  · have : dir = false := by cases dir <;> simp_all
    subst this
    simp only [rectCoef, Bool.false_eq_true, if_false, hn3, hn0, hn1, htpd, wC]
    push_cast
    rw [show ((-2 : ℤ)) ^ (n0 + n1) = (-1) ^ (n0 + n1) * 2 ^ (n0 + n1) by rw [← mul_pow]; norm_num]
    ring
  · have : dir = true := by cases dir <;> simp_all
    subst this
    simp only [rectCoef, if_true, hn3, hn0, hn1, hn2, htpd, wR]
    push_cast
    ring
  · unfold rectCoefCost
    omega

/-! ### `validE` -/

/-- The operations of `validE`. -/
def validCost (sc : ℕ) : ℕ := 130 + 16 * sc

theorem run_validE {ic im ixi m ξ : ℕ} {cheap : Bool} (hW : 8 * sc + 8 < W) (hmsc : m ≤ sc)
    (hξ : ξ < 2 ^ (2 * sc)) (hc : env.getD ic 0 = cheap.toNat) (hm : env.getD im 0 = m)
    (hx : env.getD ixi 0 = ξ) :
    Run W (validE ic im ixi) env (if validIdx cheap m ξ then 1 else 0) (validCost sc) := by
  have hmW : m < W := by omega
  have hzero : m = 0 → Run W (.ite (.var ixi) (.lit 0) (.lit 1) (.lit 0)) env
      (if validIdx true m ξ then 1 else 0) 5 := by
    intro h0
    subst h0
    refine Run.mono (Run.ite (Run.var hx) (run_lit (x := 0) (by omega))
      (fun h => (run_lit (x := 1) (by omega)).eq ?_) (fun h => (run_lit (x := 0) (by omega)).eq ?_)) (by omega)
    · rw [if_pos (show validIdx true 0 ξ from fun _ => by
        simp only [Nat.zero_sub, pow_zero, Nat.div_one]; omega)]
    · rw [if_neg (show ¬ validIdx true 0 ξ from fun hv => by
        have := hv rfl; simp only [Nat.zero_sub, pow_zero, Nat.div_one] at this; omega)]
  have hin : 1 ≤ m → Run W (.letE (markE im ixi) <|
      .ite (.add (.div (.var (ixi + 1)) (.pow2 (.sub (.var (im + 1)) (.lit 1)))) (.lit 1))
        (pow3E (.sub (.var (im + 1)) (popBE 0 (im + 1)))) (.lit 1) (.lit 0)) env
      (if validIdx true m ξ then 1 else 0) (110 + 16 * sc) := by
    intro hm1
    have hM := run_markE (W := W) (env := env) hW hmsc hm1 hm hx
    generalize hMdef : markOf m ξ = M at hM
    have hsub : Run W (.sub (.var (im + 1)) (popBE 0 (im + 1))) (M :: env) (m - popB M m)
        (1 + 1 + (2 + sc * 7)) :=
      Run.sub (Run.var (up hm)) (run_popBE (T := sc) (by omega) hmW hmsc rfl (up hm)) (small_lt hmW)
        (popB_le M m)
    have hk : m - popB M m ≤ sc := by omega
    have hpow := run_pow3E (T := sc) (by omega) hsub hk (three_pow_lt (by omega))
    have hsm : Run W (.sub (.var (im + 1)) (.lit 1)) (M :: env) (m - 1) 3 :=
      Run.mono (Run.sub (Run.var (up hm)) (run_lit (x := 1) (by omega)) (small_lt hmW) hm1) (by omega)
    have hdiv : ξ / 2 ^ (m - 1) + 1 < 2 ^ W := by
      have h1 : ξ / 2 ^ (m - 1) ≤ ξ := Nat.div_le_self _ _
      have h2 : 2 ^ (2 * sc) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hadd := Run.add (Run.div (Run.var (W := W) (up (x := M) hx)) (Run.pow2 hsm (by omega : m - 1 < W)))
      (run_lit (x := 1) (by omega)) hdiv
    have hval : validIdx true m ξ ↔ ξ / 2 ^ (m - 1) + 1 ≤ 3 ^ (m - popB M m) := by
      rw [validIdx, hMdef]
      simp only [true_implies]
      omega
    refine Run.mono (Run.letE hM (Run.ite hadd hpow
      (fun h => (run_lit (x := 1) (by omega)).eq (if_pos (hval.mpr h)).symm)
      (fun h => (run_lit (x := 0) (by omega)).eq (if_neg (fun e => h (hval.mp e))).symm))) ?_
    unfold markCost
    omega
  have hcheap : Run W (.ite (.var im) (.lit 0) (.ite (.var ixi) (.lit 0) (.lit 1) (.lit 0)) <|
      .letE (markE im ixi) <|
      .ite (.add (.div (.var (ixi + 1)) (.pow2 (.sub (.var (im + 1)) (.lit 1)))) (.lit 1))
        (pow3E (.sub (.var (im + 1)) (popBE 0 (im + 1)))) (.lit 1) (.lit 0)) env
      (if validIdx true m ξ then 1 else 0) (118 + 16 * sc) :=
    Run.mono (Run.ite (Run.var hm) (run_lit (x := 0) (by omega)) (fun h => hzero (by omega))
      (fun h => hin (by omega))) (by omega)
  refine Run.mono (Run.ite (Run.var hc) (run_lit (x := 0) (by omega))
    (fun h => (run_lit (x := 1) (by omega)).eq ?_) (fun h => hcheap.eq ?_)) ?_
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
  have hfpat := runZ_fpatTE (env := cheap.toNat :: env) (id := id + 1) (im := im + 1) (ixi := ixi + 1)
    (ip := ip + 1) (iq := iq + 1) hW hmsc hc0 (up hm) (up hx) (up hp) (up hq)
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
  have hfpat := runZ_fpatBE (env := cheap.toNat :: env) (id := id + 1) (im := im + 1) (ixi := ixi + 1)
    (ip := ir + 1) (iq := is + 1) hW hmsc hc0 (up hm) (up hx) (up hr) (up hs)
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

end DominantStrings.Pseudo
