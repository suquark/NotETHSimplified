import TransposeBase.Pseudo.CnfNetSpec

/-!
# The network of a bitset formula, as programs: the tables

The formula is a word `encF n F` in a variable. Nothing is stored between steps: ranks are nested sums.

* `validE`, `rkE`, `rkcE`: the test for an occurrence, and the ranks of occurrences and of clauses.
* `mE`, `vE`: the numbers of wires and of nodes.
* `tailTE`, `headTE`: the tables of the two ends of the wires.
-/

set_option linter.unusedSectionVars false

namespace TransposeBase.Pseudo.CnfNet

open Finset SatBase TransposeBase.General TransposeBase.Sat TransposeBase.Pseudo.CnfTree
  TransposeBase.Pseudo.Place

variable {W n : ℕ} {F : ClauseSet (SignedLiteral n)} {env : List ℕ} {nv fv : ℕ}

/-- The word is long enough for the occurrences of a formula on `n` variables. -/
structure Big (W n : ℕ) : Prop where
  big : 6 * (2 * n + 2) ^ 3 ≤ W

theorem Big.ctx (h : Big W n) : Ctx W n := ⟨by have := h.big; omega⟩

theorem cap_add_le (n : ℕ) : cap n + (2 * n + 1) ≤ (2 * n + 2) ^ 3 := by
  show (2 * n + 1) ^ 3 + (2 * n + 1) ≤ (2 * n + 2) ^ 3
  nlinarith [sq_nonneg (2 * n + 1), Nat.zero_le (n * n * n), Nat.zero_le (n * n)]

theorem Big.three_lt (h : Big W n) : 3 * cap n < W := by
  have := h.big
  have := cap_add_le n
  omega

theorem Big.two_m_lt (h : Big W n) : 2 * (n + 3 * cap n) < W := by
  have := h.big
  have := cap_add_le n
  omega

theorem Big.lt_pow (h : Big W n) {x : ℕ} (hx : x ≤ 3 * cap n) : x < 2 ^ W :=
  (lt_of_le_of_lt hx h.three_lt).trans Nat.lt_two_pow_self

theorem Big.m_lt_pow (h : Big W n) {x : ℕ} (hx : x ≤ 2 * (n + 3 * cap n)) : x < 2 ^ W :=
  (lt_of_le_of_lt hx h.two_m_lt).trans Nat.lt_two_pow_self

theorem G_le_three_cap (n : ℕ) : 2 * n + 1 ≤ 3 * cap n := by
  have := Ctx.G_le_cap n
  omega

/-! ### Digits and tests -/

/-- The digit `o % 3` of the code `o / 3`. -/
def digitE (nv o : ℕ) : Expr :=
  .letE (.div (.var o) (.lit 3)) <| .letE (.mod (.var (o + 1)) (.lit 3)) <| .letE (gE (nv + 2)) <|
    digE 2 0 1

theorem run_three (h : Big W n) : Run W (.lit 3) env 3 1 :=
  run_lit (h.lt_pow (by have := Nat.one_le_pow 3 (2 * n + 1) (by omega); show 3 ≤ 3 * (2 * n + 1) ^ 3; omega))

theorem run_digitE (h : Big W n) (hn : env.getD nv 0 = n) {o x : ℕ} (ho : env.getD o 0 = x) :
    Run W (digitE nv o) env (dg n (x / 3) (x % 3)) 24 := by
  have hi : x % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h1 : Run W (.div (.var o) (.lit 3)) env (x / 3) 3 := run_div (run_var ho) (run_three h)
  have h2 : Run W (.mod (.var (o + 1)) (.lit 3)) ((x / 3) :: env) (x % 3) 3 :=
    run_mod (run_var (gd _ ho)) (run_three h)
  have h3 : Run W (gE (nv + 2)) ((x % 3) :: (x / 3) :: env) (2 * n + 1) 5 :=
    run_g h.ctx (gd _ (gd _ hn))
  have h4 : Run W (digE 2 0 1) ((2 * n + 1) :: (x % 3) :: (x / 3) :: env) (dg n (x / 3) (x % 3)) 10 := by
    have hpow : (2 * n + 1) ^ (x % 3) < 2 ^ W := by
      refine h.lt_pow ?_
      calc (2 * n + 1) ^ (x % 3) ≤ (2 * n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ 3 * cap n := by show (2 * n + 1) ^ 3 ≤ 3 * (2 * n + 1) ^ 3; omega
    refine ⟨?_, ?_⟩
    · rw [eval_digE W _ _ _ _ (by simpa using hpow)]
      simp [dg]
    · have := ops_digE W 2 0 1 ((2 * n + 1) :: (x % 3) :: (x / 3) :: env)
      simp only [List.getD_cons_zero, List.getD_cons_succ] at this
      omega
  exact (run_let h1 (run_let h2 (run_let h3 h4))).mono (by norm_num)

theorem run_bitE (hW : 2 ≤ W) {f i : ℕ} {fv' iv : ℕ} (hf : env.getD f 0 = fv') (hi : env.getD i 0 = iv)
    (hlt : iv < W) : Run W (bitE f i) env (fv'.testBit iv).toNat 6 := by
  refine ⟨?_, (ops_bitE W f i env).le⟩
  rw [eval_bitE W f i env hW (by rwa [hi]), hf, hi]

theorem ind_testBit (x i : ℕ) : ind (x.testBit i = true) = (x.testBit i).toNat := by
  cases h : x.testBit i <;> simp [ind]

/-- The test for an occurrence. -/
def validE (nv fv o : ℕ) : Expr :=
  tAnd (.letE (.div (.var o) (.lit 3)) (bitE (fv + 1) 0)) (tNot (tLe (digitE nv o) (.lit 0)))

theorem test_validE (h : Big W n) (hF : Wide3 F) (hn : env.getD nv 0 = n)
    (hf : env.getD fv 0 = encF n F) {o x : ℕ} (ho : env.getD o 0 = x) (hx : x < 3 * cap n) :
    Test W (validE nv fv o) env (validN n F x) 43 := by
  have hw1 := h.ctx.one_le
  have hk : x / 3 < cap n := by omega
  have hkW : x / 3 < W := hk.trans h.ctx.cap_lt
  have h1 : Test W (.letE (.div (.var o) (.lit 3)) (bitE (fv + 1) 0)) env
      ((encF n F).testBit (x / 3) = true) 10 := by
    have a1 : Run W (.div (.var o) (.lit 3)) env (x / 3) 3 := run_div (run_var ho) (run_three h)
    have a2 := run_bitE (f := fv + 1) (i := 0) (env := (x / 3) :: env) h.ctx.two_le
      (gd _ hf) (gd0 _) hkW
    rw [← ind_testBit] at a2
    exact (run_let a1 a2).mono (by norm_num)
  have h2 : Test W (tNot (tLe (digitE nv o) (.lit 0))) env (¬ dg n (x / 3) (x % 3) ≤ 0) 30 :=
    (test_not hw1 (test_le hw1 (run_digitE h hn ho) (run_zero hw1))).mono (by norm_num)
  refine ((test_and hw1 h1 (fun _ => h2)).iff ?_).mono (by norm_num)
  rw [encF_testBit hF hk]
  simp only [validN, Nat.le_zero, ne_eq]

/-- The rank of an occurrence. -/
def rkE (nv fv x : ℕ) : Expr := .sum (.var x) (validE (nv + 1) (fv + 1) 0)

theorem run_rkE (h : Big W n) (hF : Wide3 F) (hn : env.getD nv 0 = n)
    (hf : env.getD fv 0 = encF n F) {x xv : ℕ} (hx : env.getD x 0 = xv) (hle : xv ≤ 3 * cap n) :
    Run W (rkE nv fv x) env (rk (validN n F) xv) (2 + xv * 44) := by
  have := run_sum (f := fun k => ind (validN n F k)) (B := 43) (run_var hx)
    (fun k hk => test_validE h hF (gd _ hn) (gd _ hf) (gd0 _) (by omega))
    (h.lt_pow ((rk_le _ _).trans hle))
  exact this

/-- The rank of a clause code. -/
def rkcE (fv x : ℕ) : Expr := .sum (.var x) (bitE (fv + 1) 0)

theorem run_rkcE (h : Big W n) (hF : Wide3 F) (hf : env.getD fv 0 = encF n F) {x xv : ℕ}
    (hx : env.getD x 0 = xv) (hle : xv ≤ cap n) :
    Run W (rkcE fv x) env (rk (Cl n F) xv) (2 + xv * 7) := by
  have := run_sum (f := fun k => ind (Cl n F k)) (B := 6) (run_var hx)
    (b := bitE (fv + 1) 0) (fun k hk => by
      have hk' : k < cap n := by omega
      have a2 := run_bitE (f := fv + 1) (i := 0) (env := k :: env) h.ctx.two_le (gd _ hf) (gd0 _)
        (hk'.trans h.ctx.cap_lt)
      rw [← ind_testBit, ind_congr (encF_testBit hF hk')] at a2
      exact a2)
    (h.lt_pow ((rk_le _ _).trans (by omega)))
  exact this

/-- The range of the occurrences. -/
def occCapE (nv : ℕ) : Expr := .mul (.lit 3) (capE nv)

theorem run_occCap (h : Big W n) (hn : env.getD nv 0 = n) : Run W (occCapE nv) env (3 * cap n) 19 := by
  exact (run_mul (run_three h) (run_cap h.ctx hn) (h.lt_pow le_rfl)).mono (by norm_num)

/-- The number of clauses. -/
def clE (nv fv : ℕ) : Expr := .letE (capE nv) (rkcE (fv + 1) 0)

theorem run_clE (h : Big W n) (hF : Wide3 F) (hn : env.getD nv 0 = n)
    (hf : env.getD fv 0 = encF n F) : Run W (clE nv fv) env (clN n F) (20 + cap n * 7) :=
  (run_let (run_cap h.ctx hn) (run_rkcE h hF (gd _ hf) (gd0 _) le_rfl)).mono (by omega)

/-- The number of wires. -/
def mE (nv fv : ℕ) : Expr := .add (.var nv) (.letE (occCapE nv) (rkE (nv + 1) (fv + 1) 0))

theorem run_mE (h : Big W n) (hF : Wide3 F) (hn : env.getD nv 0 = n)
    (hf : env.getD fv 0 = encF n F) : Run W (mE nv fv) env (mN n F) (24 + 3 * cap n * 44) := by
  have a := run_let (run_occCap h hn) (run_rkE h hF (gd _ hn) (gd _ hf) (gd0 _) le_rfl)
  refine (run_add (run_var hn) a (h.m_lt_pow ?_)).mono ?_
  · have := mN_le n F
    simp only [mN] at this
    omega
  · omega

/-- The number of nodes. -/
def vE (nv fv : ℕ) : Expr := .add (.add (.var nv) (clE nv fv)) (.var nv)

theorem run_vE (h : Big W n) (hF : Wide3 F) (hn : env.getD nv 0 = n)
    (hf : env.getD fv 0 = encF n F) : Run W (vE nv fv) env (vN n F) (24 + cap n * 7) := by
  have hc := clN_le_cap n F
  have hG := G_le_three_cap n
  refine (run_add (run_add (run_var hn) (run_clE h hF hn hf) (h.lt_pow ?_)) (run_var hn)
    (h.m_lt_pow ?_)).mono ?_
  · have := Nat.le_self_pow (n := 3) (by norm_num) (2 * n + 1)
    show n + clN n F ≤ 3 * (2 * n + 1) ^ 3
    show n + rk _ _ ≤ _
    have h2 : rk (Cl n F) (cap n) ≤ cap n := rk_le _ _
    show n + rk _ _ ≤ 3 * cap n
    have h3 : 2 * n + 1 ≤ cap n := Ctx.G_le_cap n
    omega
  · have h3 : 2 * n + 1 ≤ cap n := Ctx.G_le_cap n
    omega
  · omega

/-! ### Tables -/

/-- A table: the free wires, and then the valid occurrences by rank. The variable `0` of `free` is the free
wire. The variables `0`, `1` of `occ` are the rank and the occurrence. -/
def tableE (nv fv ifw : ℕ) (free occ : Expr) : Expr :=
  .add (.sum (.var nv) (.mul free (.pow2 (.mul (.var 0) (.var (ifw + 1))))))
    (.letE (occCapE nv) <| .sum (.var 0) <|
      .ite (validE (nv + 2) (fv + 2) 0) (.lit 0) (.lit 0) <|
        .letE (rkE (nv + 2) (fv + 2) 0) <|
          .mul occ (.pow2 (.mul (.add (.var (nv + 3)) (.var 0)) (.var (ifw + 3)))))

open Classical in
/-- The summand of an occurrence in a table. -/
noncomputable def tm (n : ℕ) (F : ClauseSet (SignedLiteral n)) (fw : ℕ) (ov : ℕ → ℕ) (o : ℕ) : ℕ :=
  if validN n F o then ov o * 2 ^ ((n + rk (validN n F) o) * fw) else 0

/-- The table after the occurrences below `N`. -/
noncomputable def Tb (n : ℕ) (F : ClauseSet (SignedLiteral n)) (fw : ℕ) (fr ov : ℕ → ℕ) (N : ℕ) : ℕ :=
  pk fw fr n + ∑ o ∈ range N, tm n F fw ov o

section Table

variable {fw : ℕ} {fr ov : ℕ → ℕ}

theorem Tb_succ (N : ℕ) : Tb n F fw fr ov (N + 1) = Tb n F fw fr ov N + tm n F fw ov N := by
  simp [Tb, sum_range_succ, add_assoc]

theorem Tb_lt (hfr : ∀ k < n, fr k < 2 ^ fw) {N M : ℕ}
    (hov : ∀ o < M, validN n F o → ov o < 2 ^ fw) (hN : N ≤ M) :
    Tb n F fw fr ov N < 2 ^ ((n + rk (validN n F) N) * fw) := by
  induction N with
  | zero =>
    simpa [Tb, rk] using pk_lt hfr
  | succ N ih =>
    have h1 := ih (by omega)
    rw [Tb_succ, rk_succ]
    by_cases hv : validN n F N
    · simp only [tm, if_pos hv, ind_pos hv]
      rw [← add_assoc]
      exact add_mul_lt h1 (hov N (by omega) hv)
    · simp only [tm, if_neg hv, ind_neg hv]
      simpa using h1

theorem fld_Tb_low {N : ℕ} (d : ℕ) {e : ℕ} (he : e < n + rk (validN n F) N) :
    fld fw (Tb n F fw fr ov (N + d)) e = fld fw (Tb n F fw fr ov N) e := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← add_assoc, Tb_succ]
    by_cases hv : validN n F (N + d)
    · simp only [tm, if_pos hv]
      rw [fld_add_low _ _ _ (he.trans_le (Nat.add_le_add_left (rk_mono _ (by omega)) _)), ih]
    · simp only [tm, if_neg hv, add_zero]
      exact ih

theorem fld_Tb_free (hfr : ∀ k < n, fr k < 2 ^ fw) {N k : ℕ} (hk : k < n) :
    fld fw (Tb n F fw fr ov N) k = fr k := by
  have h := fld_Tb_low (F := F) (fw := fw) (fr := fr) (ov := ov) (N := 0) N (e := k)
    (by simp [rk, hk])
  rw [zero_add] at h
  rw [h]
  simpa [Tb] using fld_pk hfr hk

theorem fld_Tb_occ (hfr : ∀ k < n, fr k < 2 ^ fw) {N M x : ℕ}
    (hov : ∀ o < M, validN n F o → ov o < 2 ^ fw) (hx : x < N) (hN : N ≤ M) (hv : validN n F x) :
    fld fw (Tb n F fw fr ov N) (n + rk (validN n F) x) = ov x := by
  obtain ⟨d, rfl⟩ : ∃ d, N = x + 1 + d := ⟨N - x - 1, by omega⟩
  rw [fld_Tb_low d (by rw [rk_succ, ind_pos hv]; omega), Tb_succ]
  simp only [tm, if_pos hv]
  exact fld_add_self (Tb_lt hfr hov (by omega)) (hov x (by omega) hv)

/-- The bound on the operations of a table. -/
def tblCost (n Bf Bo : ℕ) : ℕ :=
  25 + n * (Bf + 7) + 3 * cap n * (56 + 3 * cap n * 44 + Bo)

theorem run_tableE (h : Big W n) (hF : Wide3 F) (hn : env.getD nv 0 = n)
    (hf : env.getD fv 0 = encF n F) {ifw : ℕ} (hifw : env.getD ifw 0 = fw)
    (hfw : (n + rk (validN n F) (3 * cap n)) * fw < W)
    {free occ : Expr} {Bf Bo : ℕ}
    (hfree : ∀ k < n, Run W free (k :: env) (fr k) Bf) (hfr : ∀ k < n, fr k < 2 ^ fw)
    (hocc : ∀ o < 3 * cap n, validN n F o →
      Run W occ (rk (validN n F) o :: o :: (3 * cap n) :: env) (ov o) Bo)
    (hov : ∀ o < 3 * cap n, validN n F o → ov o < 2 ^ fw) :
    Run W (tableE nv fv ifw free occ) env (Tb n F fw fr ov (3 * cap n)) (tblCost n Bf Bo) := by
  have hw1 := h.ctx.one_le
  have hlt := Tb_lt (F := F) hfr hov (N := 3 * cap n) le_rfl
  have hW : 2 ^ ((n + rk (validN n F) (3 * cap n)) * fw) ≤ 2 ^ W :=
    Nat.pow_le_pow_right (by norm_num) hfw.le
  have htotal : Tb n F fw fr ov (3 * cap n) < 2 ^ W := hlt.trans_le hW
  have hsum1 : pk fw fr n < 2 ^ W := by
    have : pk fw fr n ≤ Tb n F fw fr ov (3 * cap n) := Nat.le_add_right _ _
    omega
  have hsum2 : ∑ o ∈ range (3 * cap n), tm n F fw ov o < 2 ^ W := by
    have : ∑ o ∈ range (3 * cap n), tm n F fw ov o ≤ Tb n F fw fr ov (3 * cap n) := Nat.le_add_left _ _
    omega
  have hsmall : ∀ x y, x * 2 ^ y ≤ pk fw fr n → x * 2 ^ y < 2 ^ W := fun x y hxy => by omega
  have hA : Run W (.sum (.var nv) (.mul free (.pow2 (.mul (.var 0) (.var (ifw + 1)))))) env (pk fw fr n)
      (2 + n * (Bf + 7)) := by
    refine (run_sum (B := Bf + 6) (f := fun k => fr k * 2 ^ (k * fw)) (run_var hn) (fun k hk => ?_) hsum1).mono ?_
    · have hkfw : k * fw < W := by
        refine lt_of_le_of_lt (Nat.mul_le_mul_right _ ?_) hfw
        omega
      have m1 : Run W (.mul (.var 0) (.var (ifw + 1))) (k :: env) (k * fw) 3 :=
        run_mul (run_var (gd0 _)) (run_var (gd _ hifw)) (hkfw.trans Nat.lt_two_pow_self)
      have m2 := run_pow2 m1 hkfw
      have hle : fr k * 2 ^ (k * fw) < 2 ^ W := by
        have h1 := add_mul_lt (fw := fw) (s := 0) (w := fr k) (α := k) (by positivity) (hfr k hk)
        rw [zero_add] at h1
        refine h1.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
        calc (k + 1) * fw ≤ (n + rk (validN n F) (3 * cap n)) * fw :=
              Nat.mul_le_mul_right _ (by omega)
          _ ≤ W := hfw.le
      exact (run_mul (hfree k hk) m2 hle).mono (by omega)
    · have e : Bf + 6 + 1 = Bf + 7 := rfl
      rw [e]
  have hbody : ∀ o < 3 * cap n, Run W (.ite (validE (nv + 2) (fv + 2) 0) (.lit 0) (.lit 0) <|
        .letE (rkE (nv + 2) (fv + 2) 0) <|
          .mul occ (.pow2 (.mul (.add (.var (nv + 3)) (.var 0)) (.var (ifw + 3)))))
      (o :: (3 * cap n) :: env) (tm n F fw ov o) (55 + 3 * cap n * 44 + Bo) := by
    intro o ho
    have hn2 : (o :: (3 * cap n) :: env).getD (nv + 2) 0 = n := by simpa using hn
    have hf2 : (o :: (3 * cap n) :: env).getD (fv + 2) 0 = encF n F := by simpa using hf
    have ht := test_validE (o := 0) (x := o) h hF hn2 hf2 (by simp) ho
    refine (run_ite (Bc := 10 + 3 * cap n * 44 + Bo) (v := tm n F fw ov o) ht (run_zero hw1) (fun hc => ?_) (fun hc => ?_)).mono ?_
    · have hnv : ¬ validN n F o := by
        intro hv
        rw [ind_pos hv] at hc
        omega
      simp only [tm, if_neg hnv]
      exact (run_zero hw1).mono (by omega)
    · have hv : validN n F o := by
        by_contra hnv
        rw [ind_neg hnv] at hc
        omega
      simp only [tm, if_pos hv]
      have hr := run_rkE (x := 0) (xv := o) h hF hn2 hf2 (by simp) ho.le
      set r := rk (validN n F) o with hrdef
      have hrr : r < rk (validN n F) (3 * cap n) := rk_lt hv ho
      have hidx : (n + r) * fw < W :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hfw
      set E : List ℕ := r :: o :: (3 * cap n) :: env with hE
      have g1 : Run W (.add (.var (nv + 3)) (.var 0)) E (n + r) 3 := by
        refine run_add (run_var (by simpa [hE] using hn)) (run_var (by simp [hE])) ?_
        exact h.m_lt_pow (by have := rk_le (validN n F) o; omega)
      have g2 : Run W (.mul (.add (.var (nv + 3)) (.var 0)) (.var (ifw + 3))) E ((n + r) * fw) 5 :=
        run_mul g1 (run_var (by simpa [hE] using hifw)) (hidx.trans Nat.lt_two_pow_self)
      have g3 := run_pow2 g2 hidx
      have hsm : ov o * 2 ^ ((n + r) * fw) < 2 ^ W := by
        have h1 := add_mul_lt (fw := fw) (s := 0) (w := ov o) (α := n + r) (by positivity) (hov o ho hv)
        rw [zero_add] at h1
        refine h1.trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
        calc (n + r + 1) * fw ≤ (n + rk (validN n F) (3 * cap n)) * fw :=
              Nat.mul_le_mul_right _ (by omega)
          _ ≤ W := hfw.le
      have g4 := run_mul (hocc o ho hv) g3 hsm
      refine (run_let hr g4).mono ?_
      have : o * 44 ≤ 3 * cap n * 44 := Nat.mul_le_mul_right _ ho.le
      omega
    · omega
  have hB : Run W (.letE (occCapE nv) <| .sum (.var 0) <|
      .ite (validE (nv + 2) (fv + 2) 0) (.lit 0) (.lit 0) <|
        .letE (rkE (nv + 2) (fv + 2) 0) <|
          .mul occ (.pow2 (.mul (.add (.var (nv + 3)) (.var 0)) (.var (ifw + 3)))))
      env (∑ o ∈ range (3 * cap n), tm n F fw ov o) (22 + 3 * cap n * (56 + 3 * cap n * 44 + Bo)) := by
    have := run_sum (env := (3 * cap n) :: env) (run_var (gd0 _)) hbody hsum2
    refine (run_let (run_occCap h hn) this).mono ?_
    have e : 55 + 3 * cap n * 44 + Bo + 1 = 56 + 3 * cap n * 44 + Bo := by ring
    rw [e]
    omega
  refine (run_add hA hB htotal).mono ?_
  simp only [tblCost]
  omega

end Table

/-! ### The two tables -/

/-- The table of the tails. -/
def tailTE (nv fv ifw : ℕ) : Expr :=
  tableE nv fv ifw (.var 0) (.div (.sub (digitE (nv + 3) 1) (.lit 1)) (.lit 2))

/-- The table of the heads. -/
def headTE (nv fv ifw : ℕ) : Expr :=
  tableE nv fv ifw (.add (.add (.var (nv + 1)) (clE (nv + 1) (fv + 1))) (.var 0))
    (.add (.var (nv + 3)) (.letE (.div (.var 1) (.lit 3)) (rkcE (fv + 4) 0)))

/-- The value of an occurrence in the table of the tails. -/
def tailOv (n o : ℕ) : ℕ := (dg n (o / 3) (o % 3) - 1) / 2

/-- The value of an occurrence in the table of the heads. -/
noncomputable def headOv (n : ℕ) (F : ClauseSet (SignedLiteral n)) (o : ℕ) : ℕ := n + rk (Cl n F) (o / 3)

/-- The value of a free wire in the table of the heads. -/
noncomputable def headFr (n : ℕ) (F : ClauseSet (SignedLiteral n)) (k : ℕ) : ℕ := n + clN n F + k

/-- The value of the table of the tails. -/
noncomputable def tailTN (n : ℕ) (F : ClauseSet (SignedLiteral n)) (fw : ℕ) : ℕ :=
  Tb n F fw id (tailOv n) (3 * cap n)

/-- The value of the table of the heads. -/
noncomputable def headTN (n : ℕ) (F : ClauseSet (SignedLiteral n)) (fw : ℕ) : ℕ :=
  Tb n F fw (headFr n F) (headOv n F) (3 * cap n)

theorem occ_of_valid (hF : Wide3 F) {o : ℕ} (hv : validN n F o) (ho : o < 3 * cap n) :
    ∃ j : OccW F, occNum j = o ∧ dg n (o / 3) (o % 3) = litCode j.2.1 ∧ o / 3 = code n j.1.1 := by
  obtain ⟨j, rfl⟩ := exists_occ hF hv ho
  exact ⟨j, rfl, occ_dg hF j, occ_div j⟩

section Tables

variable {fw : ℕ}

/-- The sizes that the tables need. -/
structure Fits (W n : ℕ) (F : ClauseSet (SignedLiteral n)) (fw : ℕ) : Prop where
  big : Big W n
  hv : vN n F < 2 ^ fw
  hfw : (mN n F + vN n F + 8) * fw ≤ W
  pos : 0 < fw

theorem Fits.mfw (h : Fits W n F fw) : (n + rk (validN n F) (3 * cap n)) * fw < W := by
  have h1 := h.hfw
  have h2 := h.pos
  calc (n + rk (validN n F) (3 * cap n)) * fw < (mN n F + vN n F + 8) * fw := by
        refine Nat.mul_lt_mul_of_pos_right ?_ h2
        simp only [mN]
        omega
    _ ≤ W := h1

theorem tailOv_lt (h : Fits W n F fw) (hF : Wide3 F) {o : ℕ} (ho : o < 3 * cap n) (hv : validN n F o) :
    tailOv n o < 2 ^ fw := by
  obtain ⟨j, -, hd, -⟩ := occ_of_valid hF hv ho
  have h1 := j.2.1.1.2
  have h2 := h.hv
  simp only [tailOv, hd, lit_var]
  simp only [vN] at h2
  omega

theorem headOv_lt (h : Fits W n F fw) (hF : Wide3 F) {o : ℕ} (ho : o < 3 * cap n) (hv : validN n F o) :
    headOv n F o < 2 ^ fw := by
  have h1 : rk (Cl n F) (o / 3) < clN n F := rk_lt hv.1 (by omega)
  have h2 := h.hv
  simp only [headOv]
  simp only [vN] at h2
  omega

theorem headFr_lt (h : Fits W n F fw) {k : ℕ} (hk : k < n) : headFr n F k < 2 ^ fw := by
  have h2 := h.hv
  simp only [headFr]
  simp only [vN] at h2
  omega

theorem free_lt (h : Fits W n F fw) {k : ℕ} (hk : k < n) : id k < 2 ^ fw := by
  have h2 := h.hv
  simp only [vN] at h2
  simp only [id]
  omega

theorem run_tailTE (h : Fits W n F fw) (hF : Wide3 F) (hn : env.getD nv 0 = n)
    (hf : env.getD fv 0 = encF n F) {ifw : ℕ} (hifw : env.getD ifw 0 = fw) :
    Run W (tailTE nv fv ifw) env (tailTN n F fw) (tblCost n 1 28) := by
  refine run_tableE h.big hF hn hf hifw h.mfw (fr := id) (ov := tailOv n)
    (fun k _ => run_var (gd0 _)) (fun k hk => free_lt h hk) (fun o ho hv => ?_)
    (fun o ho hv => tailOv_lt h hF ho hv)
  have hw1 := h.big.ctx.one_le
  have hd := run_digitE (nv := nv + 3) (o := 1) (x := o)
    (env := rk (validN n F) o :: o :: (3 * cap n) :: env) h.big (by simpa using hn) (by simp)
  have hpos : 1 ≤ dg n (o / 3) (o % 3) := Nat.pos_of_ne_zero hv.2
  have hlt : dg n (o / 3) (o % 3) < 2 ^ W := h.big.lt_pow ((dg_lt _ _ _).le.trans (G_le_three_cap n))
  have h2lit : (2 : ℕ) < 2 ^ W := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) h.big.ctx.two_le
  exact (run_div (run_sub hd (run_one hw1) hpos hlt) (run_lit h2lit)).mono (by omega)

theorem run_headTE (h : Fits W n F fw) (hF : Wide3 F) (hn : env.getD nv 0 = n)
    (hf : env.getD fv 0 = encF n F) {ifw : ℕ} (hifw : env.getD ifw 0 = fw) :
    Run W (headTE nv fv ifw) env (headTN n F fw) (tblCost n (24 + cap n * 7) (9 + cap n * 7)) := by
  have hbound : ∀ x, x ≤ vN n F → x < 2 ^ W := fun x hx => by
    have h1 := vN_le hF
    have h2 := mN_le n F
    exact h.big.m_lt_pow (by have := Ctx.G_le_cap n; omega)
  refine run_tableE h.big hF hn hf hifw h.mfw (fr := headFr n F) (ov := headOv n F)
    (fun k hk => ?_) (fun k hk => headFr_lt h hk) (fun o ho hv => ?_)
    (fun o ho hv => headOv_lt h hF ho hv)
  · have hc := run_clE (env := k :: env) (nv := nv + 1) (fv := fv + 1) h.big hF (gd _ hn) (gd _ hf)
    have a1 := run_add (run_var (gd k hn)) hc (hbound _ (by simp only [vN]; omega))
    exact (run_add a1 (run_var (gd0 _)) (hbound _ (by simp only [vN]; omega))).mono (by omega)
  · set E : List ℕ := rk (validN n F) o :: o :: (3 * cap n) :: env with hE
    have h1 : Run W (.div (.var 1) (.lit 3)) E (o / 3) 3 :=
      run_div (run_var (by simp [hE])) (run_three h.big)
    have hk : o / 3 ≤ cap n := by omega
    have h2 := run_rkcE (fv := fv + 4) (x := 0) (xv := o / 3) (env := (o / 3) :: E) h.big hF
      (by simpa [hE] using hf) (by simp) hk
    have h3 := run_let h1 h2
    have hr : rk (Cl n F) (o / 3) < clN n F := rk_lt hv.1 (by omega)
    have h4 := run_add (run_var (i := nv + 3) (env := E) (by simpa [hE] using hn)) h3
      (hbound _ (by simp only [vN]; omega))
    refine h4.mono ?_
    have : o / 3 * 7 ≤ cap n * 7 := Nat.mul_le_mul_right _ hk
    omega

/-- **The tables decode to the network.** -/
theorem netT (h : Fits W n F fw) (hF : Wide3 F) :
    NetT fw (tailTN n F fw) (headTN n F fw) (tailN hF) (headN hF) := by
  have hfr1 : ∀ k < n, id k < 2 ^ fw := fun k hk => free_lt h hk
  have hfr2 : ∀ k < n, headFr n F k < 2 ^ fw := fun k hk => headFr_lt h hk
  constructor
  · intro e
    obtain ⟨w, rfl⟩ := (eW hF).surjective e
    cases w with
    | inl u =>
      rw [tail_inl, eW_val]
      simp only [wireNum]
      exact fld_Tb_free hfr1 u.2
    | inr j =>
      rw [tail_inr, eW_val]
      simp only [wireNum]
      have := fld_Tb_occ (F := F) (fw := fw) (fr := id) (ov := tailOv n) hfr1
        (fun o ho hv => tailOv_lt h hF ho hv) (occ_lt hF j) le_rfl (valid_occ hF j)
      rw [tailTN, this, tailOv, occ_dg hF, lit_var]
  · intro e
    obtain ⟨w, rfl⟩ := (eW hF).surjective e
    cases w with
    | inl u =>
      rw [head_inl, eW_val]
      simp only [wireNum]
      exact fld_Tb_free hfr2 u.2
    | inr j =>
      rw [head_inr, eW_val]
      simp only [wireNum]
      have := fld_Tb_occ (F := F) (fw := fw) (fr := headFr n F) (ov := headOv n F) hfr2
        (fun o ho hv => headOv_lt h hF ho hv) (occ_lt hF j) le_rfl (valid_occ hF j)
      rw [headTN, this, headOv, occ_div]

theorem tailTN_lt (h : Fits W n F fw) (hF : Wide3 F) : tailTN n F fw < 2 ^ (mN n F * fw) :=
  Tb_lt (fun k hk => free_lt h hk) (fun o ho hv => tailOv_lt h hF ho hv) le_rfl

theorem headTN_lt (h : Fits W n F fw) (hF : Wide3 F) : headTN n F fw < 2 ^ (mN n F * fw) :=
  Tb_lt (fun k hk => headFr_lt h hk) (fun o ho hv => headOv_lt h hF ho hv) le_rfl

end Tables

end TransposeBase.Pseudo.CnfNet
