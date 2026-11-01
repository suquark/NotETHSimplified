import OnePigeonhole.Pseudo.LeafCell

/-!
# One side of one cube

The row of the table, the sum over the exponent vectors, and the five words of the corners. The program computes the value `sideK` of one
side at a key given by two numbers and a layer (`runZ_sideE`). The words are over all corners with no test for the side or the use. The
sign of the cube needs no code: `sideS` holds it.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf

namespace Cost

def row : ℕ := 26
def look : ℕ := 15
def mono (T : ℕ) : ℕ := 1 + 1 + T * ((1 + dig T + (1 + dig T + (1 + 1 + T * (1 + 1)))) + 1)
def sideSum (T Bx : ℕ) : ℕ := 1 + 1 + Bx * ((1 + look + mono T) + 1)
/-- The body of the word of `x̃`. -/
def xBody : ℕ := 1 + bit + 1 + (bit + bit)
/-- The body of the word of `y`. -/
def yBody : ℕ := 8
def side (T Bx : ℕ) : ℕ :=
  1 + word T 1 + (1 + word T bit + (1 + word T bit + (1 + word T xBody + (1 + word T yBody +
    (1 + row + sideSum T Bx)))))

end Cost

variable {S : Setup} {c : Ctx} {env : List ℕ}

namespace Setup

variable (S : Setup)

theorem wid_lt : Lits.wid S.m S.lt < S.W := S.big.hlit

theorem f_lt : S.lt.f < S.W := by
  have := S.wid_lt
  unfold Lits.wid at this
  omega

theorem f_mul_lt : S.lt.f * sSize S.Q < S.W := by
  have := S.wid_lt
  unfold Lits.wid at this
  simp only [Q]
  omega

theorem sSize_lt : sSize S.Q < S.W := by
  have := S.wid_lt
  unfold Lits.wid at this
  simp only [Q]
  omega

theorem sT_lt : S.lt.sT < 2 ^ S.W := S.hlt.sT_lt.trans (S.pow_lt_W S.f_mul_lt)

theorem Q_lt_W : S.Q < S.W := by have := S.Q_le_T; have := S.T_lt_W; omega

theorem two_pow_Q_lt_W : 2 ^ S.Q < S.W := by have := S.two_pow_Q_le_T; have := S.T_lt_W; omega

theorem Bx_pos : 0 < S.Bx := by simp only [Bx, Eb]; positivity

theorem rows_pos : 0 < sRows S.Q := by
  have := S.Q_pos
  unfold sRows pwN
  positivity

theorem Bx_le_size : S.Bx ≤ sSize S.Q := Nat.le_mul_of_pos_left _ S.rows_pos

theorem Bx_lt_W : S.Bx < S.W := lt_of_le_of_lt S.Bx_le_size S.sSize_lt

theorem Eb_pow_lt {i : ℕ} (hi : i ≤ S.Q) : S.Eb ^ i < 2 ^ S.W := by
  have h1 : S.Eb ^ i ≤ S.Bx := Nat.pow_le_pow_right (Nat.succ_pos _) hi
  exact S.lt_pow_W (lt_of_le_of_lt h1 S.Bx_lt_W)

end Setup

/-! ### The row of the table -/

/-- The row of the table, for the numbers in variables. -/
def rowE (c : Ctx) (t b Dw PT PS xw yw : ℕ) : Expr :=
  pkE (.var c.Pw) (pkE (.var c.Pw) (pkE (.var c.Pw) (pkE (.var c.Pw) (pkE (.var c.Pw)
    (pkE (.lit 2) (.var t) (.lit b)) (.var Dw)) (.var PT)) (.var PS)) (.var xw)) (.var yw)

theorem run_rowE (h : Agree S c env) {t b Dw PT PS xw yw tv Dv PTv PSv xv yv : ℕ} (hb : b < 2)
    (ht : env.getD t 0 = tv) (hD : env.getD Dw 0 = Dv) (h1 : env.getD PT 0 = PTv) (h2 : env.getD PS 0 = PSv)
    (h4 : env.getD xw 0 = xv) (h5 : env.getD yw 0 = yv)
    (hlt : sBase S.Q tv b Dv PTv PSv xv yv < 2 ^ S.W) :
    Run S.W (rowE c t b Dw PT PS xw yw) env (sBase S.Q tv b Dv PTv PSv xv yv) Cost.row := by
  have hP : 0 < S.Pw := by positivity
  have hPr : Run S.W (.var c.Pw) env S.Pw 1 := Run.var h.Pw
  unfold sBase at hlt
  have l5 := hlt
  have l4 := lt_of_le_of_lt (pk_le _ hP) l5
  have l3 := lt_of_le_of_lt (pk_le _ hP) l4
  have l2 := lt_of_le_of_lt (pk_le _ hP) l3
  have l1 := lt_of_le_of_lt (pk_le _ hP) l2
  have l0 := lt_of_le_of_lt (pk_le _ hP) l1
  have r0 := run_pkE (Run.var ht) (Run.lit (two_lt_W S)) (Run.lit (lt_of_lt_of_le hb (two_lt_W S).le)) l0
  have r1 := run_pkE r0 hPr (Run.var hD) l1
  have r2 := run_pkE r1 hPr (Run.var h1) l2
  have r3 := run_pkE r2 hPr (Run.var h2) l3
  have r4 := run_pkE r3 hPr (Run.var h4) l4
  have r5 := run_pkE r4 hPr (Run.var h5) l5
  exact r5.mono (by norm_num [Cost.row])

/-! ### Lookups -/

/-- Read the literal table at the position `idx`, and subtract the offset. -/
def lookE (c : Ctx) (T : ℕ) (idx : Expr) : Expr :=
  .sub (.mod (.div (.lit T) (.pow2 (.mul idx (.lit c.lt.f)))) (.pow2 (.lit c.lt.f))) (.lit c.lt.off)

theorem runZ_lookE (h : Agree S c env) {T : ℕ} {idx : Expr} {I ci : ℕ} (hi : Run S.W idx env I ci)
    (hT : T < 2 ^ S.W) (hI : I * S.lt.f < S.W) :
    RunZ S.W (lookE c T idx) env (((fld S.lt.f T I : ℕ) : ℤ) - S.lt.off) (10 + ci) := by
  unfold lookE
  rw [h.lt]
  have hf := S.f_lt
  have h1 := Run.mod (Run.div (Run.lit (env := env) hT) (Run.pow2 (Run.mul hi (Run.lit (env := env) (S.lt_pow_W hf))
    (S.lt_pow_W hI)) hI)) (Run.pow2 (Run.lit (env := env) (S.lt_pow_W hf)) hf)
  exact (RunZ.sub h1.toZ (RunZ.lit S.lt.off)).mono (by omega)

/-! ### The loop variables -/

/-- The indices of the global values and of the outer loop variables. -/
structure Loc where
  c : Ctx
  t : ℕ
  mT : ℕ
  mS : ℕ
  mU : ℕ
  p : ℕ
  as : ℕ
  node : Expr

/-- One more binder. -/
def Loc.up (l : Loc) : Loc :=
  ⟨l.c.up, l.t + 1, l.mT + 1, l.mS + 1, l.mU + 1, l.p + 1, l.as + 1, l.node⟩

/-- The values of the outer loop variables. -/
structure LV (S : Setup) where
  t : Fin S.Q
  mT : ℕ
  mS : ℕ
  mU : ℕ
  p : ℕ
  A : ℕ

/-- The environment holds the outer loop variables. -/
structure Frame (S : Setup) (l : Loc) (V : LV S) (env : List ℕ) : Prop where
  ag : Agree S l.c env
  t : env.getD l.t 0 = V.t
  mT : env.getD l.mT 0 = V.mT
  mS : env.getD l.mS 0 = V.mS
  mU : env.getD l.mU 0 = V.mU
  p : env.getD l.p 0 = V.p
  as : env.getD l.as 0 = V.A
  node : l.node = S.nodeE

theorem Frame.up {l : Loc} {V : LV S} (h : Frame S l V env) (x : ℕ) : Frame S l.up V (x :: env) :=
  ⟨h.ag.up x, h.t, h.mT, h.mS, h.mU, h.p, h.as, h.node⟩

variable {l : Loc} {V : LV S}

/-! ### The monomial -/

/-- The value of `p ^ e` at the grid point in variable `p` and the exponent vector in variable `e`. -/
def monoE (c : Ctx) (e p : ℕ) : Expr :=
  .prod (.var c.Q) (.letE (digE (e + 1) c.up.Eb 0)
    (.letE (digE (p + 2) c.up.up.Nq 1) (.prod (.var 1) (.var 1))))

theorem runZ_monoE (h : Agree S c env) {e p Ev P : ℕ} (he : env.getD e 0 = Ev) (hp : env.getD p 0 = P) :
    RunZ S.W (monoE c e p) env (∏ i, ((S.pN P i : ℕ) : ℤ) ^ (S.eOf Ev i : ℕ)) (Cost.mono S.T) := by
  refine RunZ.prodFin (Run.var h.Q) S.Q_le_T fun i => ?_
  have hi := i.2
  have hup := h.up (i : ℕ)
  have hiT := hi.le.trans S.Q_le_T
  have h1 : Run S.W (digE (e + 1) c.up.Eb 0) ((i : ℕ) :: env) (dig S.Eb Ev i) (Cost.dig S.T) :=
    Run.digE he hup.Eb rfl hiT (S.Eb_pow_lt hi.le)
  have hup2 := hup.up (dig S.Eb Ev i)
  have h2 : Run S.W (digE (p + 2) c.up.up.Nq 1) (dig S.Eb Ev i :: (i : ℕ) :: env) (dig S.Nq P i) (Cost.dig S.T) :=
    Run.digE hp hup2.Nq rfl hiT (S.Nq_pow_lt hi.le)
  have hEb : dig S.Eb Ev i ≤ S.T := by
    have h3 : dig S.Eb Ev i < 2 ^ S.Q + 1 := dig_lt (Nat.succ_pos _) _ _
    have h4 := S.two_pow_Q_le_T
    omega
  have hq : RunZ S.W (.prod (.var 1) (.var 1)) (dig S.Nq P i :: dig S.Eb Ev i :: (i : ℕ) :: env)
      (∏ _j ∈ range (dig S.Eb Ev i), (dig S.Nq P i : ℤ)) (1 + 1 + S.T * (1 + 1)) :=
    RunZ.prod (Run.var rfl) hEb (fun j _ => (Run.var rfl).toZ)
  rw [Finset.prod_const, card_range] at hq
  exact RunZ.letE h1 (RunZ.letE h2 hq)

/-! ### The sum over the exponent vectors -/

/-- The sum over the exponent vectors, for the row in variable `0`. -/
def sideSumE (l : Loc) : Expr :=
  .sum (.var l.c.Bx)
    (.mul (lookE l.c.up l.c.lt.sT (.add (.mul (.var 1) (.var l.c.up.Bx)) (.var 0)))
      (monoE l.c.up 0 (l.p + 1)))

theorem runZ_sideSumE (h : Frame S l V env) {Dw PTw PSw xw yw : ℕ} {b : Bool}
    (h0 : env.getD 0 0 = sBase S.Q V.t b.toNat Dw PTw PSw xw yw)
    (h1 : Dw < S.Pw) (h2 : PTw < S.Pw) (h3 : PSw < S.Pw) (h4 : xw < S.Pw) (h5 : yw < S.Pw) :
    RunZ S.W (sideSumE l) env (sideZ S.lt.D S.R V.t Dw b PTw PSw xw yw (S.pN V.p)) (Cost.sideSum S.T S.Bx) := by
  unfold sideZ sideSumE
  rw [Code.sum_word_succ (2 ^ S.Q) S.Q, h.ag.lt]
  have hsz := S.sSize_lt
  have hf := S.f_mul_lt
  have hb : b.toNat < 2 := by cases b <;> simp
  refine RunZ.sum (Run.var h.ag.Bx) le_rfl fun k hk => ?_
  have hup := h.up k
  have hidx : sIdx S.Q V.t b.toNat Dw PTw PSw xw yw k < sSize S.Q :=
    sIdx_lt V.t.2 hb h1 h2 h3 h4 h5 hk
  have hrun : Run S.W (.add (.mul (.var 1) (.var l.c.up.Bx)) (.var 0)) (k :: env)
      (sIdx S.Q V.t b.toNat Dw PTw PSw xw yw k) 5 := by
    have hbase : ((k :: env).getD 1 0) = sBase S.Q V.t b.toNat Dw PTw PSw xw yw := h0
    have hk0 : Run S.W (.var 0) (k :: env) k 1 := Run.var rfl
    exact (Run.add (Run.mul (Run.var hbase) (Run.var hup.ag.Bx)
      (lt_of_le_of_lt (Nat.le_add_right _ k) (S.lt_pow_W (hidx.trans hsz)))) hk0
      (S.lt_pow_W (hidx.trans hsz))).mono (by omega)
  have hI : sIdx S.Q V.t b.toNat Dw PTw PSw xw yw k * S.lt.f < S.W := by
    have : sIdx S.Q V.t b.toNat Dw PTw PSw xw yw k * S.lt.f ≤ S.lt.f * sSize S.Q := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ hidx.le
    omega
  have hl := runZ_lookE hup.ag hrun S.sT_lt hI
  have hc := S.hlt.coef V.t b Dw PTw PSw xw yw h1 h2 h3 h4 h5 (wordOf (Nat.succ_pos (2 ^ S.Q)) S.Q k)
  rw [Code.wordIdx_wordOf (Nat.succ_pos _) hk] at hc
  rw [hc] at hl
  have hm : RunZ S.W (monoE l.c.up 0 (l.p + 1)) (k :: env) _ (Cost.mono S.T) :=
    runZ_monoE hup.ag (e := 0) (Ev := k) rfl (P := V.p) h.p
  exact (RunZ.mul hl hm).mono (by simp only [Cost.look]; omega)

/-! ### One side -/

/-- The bit of `x̃` at the wire in variable `0`: the bit of `MU` if the wire is in `MS`, and the `x` copy of the assignment if not. -/
def xBodyE (mS mU as : ℕ) : Expr :=
  .ite (bitX mS (.var 0)) (.lit 0) (bitX as (.var 0)) (bitX mU (.var 0))

/-- The scaled value of the side `b` of the cube with the numbers in the variables `u`, `w`, `ll`. -/
def sideE (l : Loc) (b u w ll : ℕ) : Expr :=
  .letE (wordE l.c (.lit 1) u w ll) <|
  .letE (wordE l.c.up (bitX (l.mT + 5) (.var 0)) (u + 1) (w + 1) (ll + 1)) <|
  .letE (wordE l.c.up.up (bitX (l.mS + 6) (.var 0)) (u + 2) (w + 2) (ll + 2)) <|
  .letE (wordE l.c.up.up.up (xBodyE (l.mS + 7) (l.mU + 7) (l.as + 7)) (u + 3) (w + 3) (ll + 3)) <|
  .letE (wordE l.c.up.up.up.up (bitX (l.as + 8) (.add (.var 0) (.var (l.c.M + 8)))) (u + 4) (w + 4) (ll + 4)) <|
  .letE (rowE l.c.up.up.up.up.up (l.t + 5) b 4 3 2 1 0) <|
  sideSumE l.up.up.up.up.up.up

theorem memB_setS (x : ℕ) (e : Fin S.M) : (memB (S.setS x) e).toNat = (x.testBit e).toNat := by
  unfold memB
  cases hb : x.testBit e
  · have : e ∉ S.setS x := fun h => by
      have := S.mem_setS.mp h
      rw [hb] at this
      exact Bool.noConfusion this
    simp [this]
  · have : e ∈ S.setS x := S.mem_setS.mpr hb
    simp [this]

/-- The bit of `x̃` as a program. -/
theorem run_xBodyE {E : List ℕ} {mS mU as MS MU A : ℕ} (e : Fin S.M) (h0 : E.getD 0 0 = e) (h1 : E.getD mS 0 = MS)
    (h2 : E.getD mU 0 = MU) (h3 : E.getD as 0 = A) :
    Run S.W (xBodyE mS mU as) E (xtB (S.setS MS) (S.setS MU) (asgX S.M A) e).toNat Cost.xBody := by
  have hW : (e : ℕ) < S.W := by have := e.2; have := S.M_le_T; have := S.T_lt_W; omega
  have r1 : Run S.W (bitX mS (.var 0)) E (MS.testBit e).toNat Cost.bit := run_bitV h1 h0 hW
  have r2 : Run S.W (bitX as (.var 0)) E (A.testBit e).toNat Cost.bit := run_bitV h3 h0 hW
  have r3 : Run S.W (bitX mU (.var 0)) E (MU.testBit e).toNat Cost.bit := run_bitV h2 h0 hW
  refine Run.ite r1 (Run.lit (by positivity)) (fun hle => r2.eq ?_) (fun hle => r3.eq ?_)
  · have h4 : MS.testBit e = false := by
      cases hq : MS.testBit e
      · rfl
      · simp [hq] at hle
    have h5 : e ∉ S.setS MS := fun h => by
      have := S.mem_setS.mp h
      rw [h4] at this
      exact Bool.noConfusion this
    simp only [xtB, if_neg h5, asgX]
  · have h4 : MS.testBit e = true := by
      cases hq : MS.testBit e
      · simp [hq] at hle
      · rfl
    have h5 : e ∈ S.setS MS := S.mem_setS.mpr h4
    simp only [xtB, if_pos h5]
    exact (memB_setS MU e).symm

theorem runZ_sideE (h : Frame S l V env) (b : Bool) {u w ll U Vv : ℕ} {ℓ : Fin S.h} (hu : env.getD u 0 = U)
    (hw : env.getD w 0 = Vv) (hl : env.getD ll 0 = ℓ) (hU : U < S.K) (hV : Vv < S.K) :
    RunZ S.W (sideE l b.toNat u w ll) env
      (sideK S.lt.D S.R S.wi V.t (S.pN V.p) (S.setS V.mT) (S.setS V.mS) (S.setS V.mU) (asgX S.M V.A) (asgY S.M V.A)
        (S.keyN U Vv ℓ) b)
      (Cost.side S.T S.Bx) := by
  set k := S.keyN U Vv ℓ with hk
  have hMW : ∀ e : Fin S.M, (e : ℕ) < S.W := fun e => by
    have := e.2; have := S.M_le_T; have := S.T_lt_W; omega
  set Dv := fullWord S.wi k (fun _ => true) with hDv
  set PTv := fullWord S.wi k (memB (S.setS V.mT)) with hPT
  set PSv := fullWord S.wi k (memB (S.setS V.mS)) with hPS
  set xv := fullWord S.wi k (xtB (S.setS V.mS) (S.setS V.mU) (asgX S.M V.A)) with hxv
  set yv := fullWord S.wi k (asgY S.M V.A) with hyv
  have r0 : Run S.W (wordE l.c (.lit 1) u w ll) env Dv (Cost.word S.T 1) :=
    run_wordE h.ag hu hw hl hU hV fun e V' U' i => Run.lit (one_lt_W S)
  have f1 := h.up Dv
  have r1 : Run S.W (wordE l.c.up (bitX (l.mT + 5) (.var 0)) (u + 1) (w + 1) (ll + 1)) (Dv :: env) PTv
      (Cost.word S.T Cost.bit) :=
    run_wordE f1.ag hu hw hl hU hV fun e V' U' i =>
      have hq : ((e : ℕ) :: V' :: U' :: i :: Dv :: env).getD (l.mT + 5) 0 = V.mT := h.mT
      (run_bitV (S := S) (i := 0) (I := e) hq rfl (hMW e)).eq (memB_setS _ e).symm
  have f2 := f1.up PTv
  have r2 : Run S.W (wordE l.c.up.up (bitX (l.mS + 6) (.var 0)) (u + 2) (w + 2) (ll + 2)) (PTv :: Dv :: env) PSv
      (Cost.word S.T Cost.bit) :=
    run_wordE f2.ag hu hw hl hU hV fun e V' U' i =>
      have hq : ((e : ℕ) :: V' :: U' :: i :: PTv :: Dv :: env).getD (l.mS + 6) 0 = V.mS := h.mS
      (run_bitV (S := S) (i := 0) (I := e) hq rfl (hMW e)).eq (memB_setS _ e).symm
  have f3 := f2.up PSv
  have r3 : Run S.W (wordE l.c.up.up.up (xBodyE (l.mS + 7) (l.mU + 7) (l.as + 7)) (u + 3) (w + 3) (ll + 3))
      (PSv :: PTv :: Dv :: env) xv (Cost.word S.T Cost.xBody) :=
    run_wordE f3.ag hu hw hl hU hV fun e V' U' i => run_xBodyE e rfl h.mS h.mU h.as
  have f4 := f3.up xv
  have r4 : Run S.W (wordE l.c.up.up.up.up (bitX (l.as + 8) (.add (.var 0) (.var (l.c.M + 8)))) (u + 4) (w + 4) (ll + 4))
      (xv :: PSv :: PTv :: Dv :: env) yv (Cost.word S.T Cost.yBody) := by
    refine run_wordE f4.ag hu hw hl hU hV fun e V' U' i => ?_
    have hs : S.M + (e : ℕ) < S.W := by
      have := S.T_lt_W; have := S.M_le_T; have := e.2; simp only [Setup.T] at *; omega
    have hq : ((e : ℕ) :: V' :: U' :: i :: xv :: PSv :: PTv :: Dv :: env).getD (l.c.M + 8) 0 = S.M := h.ag.M
    have hq2 : ((e : ℕ) :: V' :: U' :: i :: xv :: PSv :: PTv :: Dv :: env).getD (l.as + 8) 0 = V.A := h.as
    have hadd : Run S.W (.add (.var 0) (.var (l.c.M + 8))) ((e : ℕ) :: V' :: U' :: i :: xv :: PSv :: PTv :: Dv :: env)
        (S.M + e) 3 :=
      ((Run.add (x := e) (y := S.M) (Run.var rfl) (Run.var hq) (S.lt_pow_W (by omega))).eq (by omega)).mono (by omega)
    exact (Run.bitX hq2 hadd hs S.W_two).mono (by simp only [Cost.yBody]; omega)
  have f5 := f4.up yv
  have hb : b.toNat < 2 := by cases b <;> simp
  have hDl : Dv < S.Pw := patWord_lt _
  have hPTl : PTv < S.Pw := patWord_lt _
  have hPSl : PSv < S.Pw := patWord_lt _
  have hxl : xv < S.Pw := patWord_lt _
  have hyl : yv < S.Pw := patWord_lt _
  have hrowlt : sBase S.Q V.t b.toNat Dv PTv PSv xv yv < 2 ^ S.W := by
    have h1 : sBase S.Q V.t b.toNat Dv PTv PSv xv yv < sRows S.Q :=
      sBase_lt V.t.2 hb hDl hPTl hPSl hxl hyl
    have h2 : sRows S.Q ≤ sSize S.Q := Nat.le_mul_of_pos_right _ S.Bx_pos
    exact S.lt_pow_W ((lt_of_lt_of_le h1 h2).trans S.sSize_lt)
  have r5 : Run S.W (rowE l.c.up.up.up.up.up (l.t + 5) b.toNat 4 3 2 1 0)
      (yv :: xv :: PSv :: PTv :: Dv :: env) (sBase S.Q V.t b.toNat Dv PTv PSv xv yv) Cost.row :=
    run_rowE f5.ag hb f5.t rfl rfl rfl rfl rfl hrowlt
  have f6 := f5.up (sBase S.Q V.t b.toNat Dv PTv PSv xv yv)
  have r6 := runZ_sideSumE f6 (b := b) rfl hDl hPTl hPSl hxl hyl
  exact RunZ.letE r0 (RunZ.letE r1 (RunZ.letE r2 (RunZ.letE r3 (RunZ.letE r4 (RunZ.letE r5 r6)))))

end OnePigeonhole.Pseudo.Leaf
