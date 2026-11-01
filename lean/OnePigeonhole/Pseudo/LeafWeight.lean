import OnePigeonhole.Pseudo.LeafGroup

/-!
# The weight of a grid point and the next mask

The integer weight of a grid point is a product over the coordinates of sums over the allowed exponents. The next mask is computed
from the bits of the current mask, and it stays fixed from `2 ^ M` on. The test of the masks is `|MT| ≤ r` and `MU ⊆ MS`, and it comes
with the sign `(-1) ^ |MT|`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf

namespace Cost

def lag (T : ℕ) : ℕ := 16 * T + 50
/-- The cost of the term of one exponent. -/
def wtTerm (T : ℕ) : ℕ :=
  1 + (1 + 1 + 1) + 1 + ((1 + 1 + 1 + (lag T + 1)) +
    (1 + 1 + 1 + ((1 + (1 + 1 + 1) + 1 + (lag T + 1)) + lag T)))
def wtBody (T : ℕ) : ℕ := 1 + dig T + (1 + 1 + T * (wtTerm T + 1))
/-- The cost of the weight of a grid point. -/
def wt (T : ℕ) : ℕ := 1 + 1 + T * (wtBody T + 1)
def popN (T : ℕ) : ℕ := 1 + 1 + T * (bit + 1)
def lowBody (T : ℕ) : ℕ := 1 + (1 + bit + (1 + 1 + T * ((1 + 1 + bit) + 1))) + (1 + 1)
def low (T : ℕ) : ℕ := 1 + 1 + T * (lowBody T + 1)
def next (T : ℕ) : ℕ :=
  1 + (1 + 1) + 1 + (1 +
    (1 + (1 + popN T + 1) + 1 + ((1 + 1 + 1) + (1 + 1 + 1 + ((1 + 1) + (1 + 1 + low T))))))
def subBits (T : ℕ) : ℕ := 1 + 1 + T * ((1 + bit + bit + (1 + 1)) + 1)
/-- The sign of a number. -/
def signV : ℕ := 1 + (1 + 1 + 1) + 1 + (1 + (1 + 1 + 1))
def cTestV (T : ℕ) : ℕ := 1 + popN T + (1 + 1 + 1 + ((1 + subBits T + 1 + (signV + 1)) + 1))

end Cost

variable {S : Setup} {c : Ctx} {env : List ℕ} {l : Loc} {V : LV S}

namespace Setup

variable (S : Setup)

/-- The integer weight of coordinate `i` at the value `b`: the sum of the allowed exponents. -/
noncomputable def wtZ (t i : Fin S.Q) (b : Fin (S.M + 1)) : ℤ :=
  ∑ e ∈ digitSet S.M S.J t i, Lag.lagZ S.M e b

/-- The integer weight of a grid point. -/
noncomputable def wZ (t : Fin S.Q) (p : Fin S.Q → Fin (S.M + 1)) : ℤ :=
  ∏ i, S.wtZ t i (p i)

theorem wZ_cast (t : Fin S.Q) (p : Fin S.Q → Fin (S.M + 1)) :
    (S.wZ t p : ℚ) = ((S.M.factorial ^ S.Q : ℕ) : ℚ) * digitWeight S.M S.J t p := by
  unfold wZ wtZ
  rw [digitWeight_eq_prod]
  push_cast
  have : ((S.M.factorial : ℚ)) ^ S.Q = ∏ _i : Fin S.Q, (S.M.factorial : ℚ) := by simp
  rw [this, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => Lag.lagZ_cast _ _ _

end Setup

/-! ### The weight -/

theorem small_J (S : Setup) : S.J ≤ S.M + 1 := by
  have h1 : S.M / S.m * S.m ≤ S.M := Nat.div_mul_le_self _ _
  have h2 : S.M / S.m * 2 ≤ S.M / S.m * S.m := Nat.mul_le_mul_left _ S.m_two
  simp only [Setup.J]
  omega

/-- The term of the exponent in variable `0`, for the value in variable `1`, the coordinate in variable `2` and the digit in variable
`t`. It tests `digitTest`. -/
def wtTermE (c : Ctx) (t : ℕ) : Expr :=
  .ite (.add (.var 2) (.lit 1)) (.var t)
    (.ite (.var c.J) (.var 0) (Lag.lagE c.M c.B 0 1) (.lit 0))
    (.ite (.var 2) (.var t)
      (.ite (.add (.var 0) (.lit 1)) (.var c.J) (Lag.lagE c.M c.B 0 1) (.lit 0))
      (Lag.lagE c.M c.B 0 1))

theorem runZ_wtTermE {e b : ℕ} {i t' : Fin S.Q} {t : ℕ} (h : Agree S c (e :: b :: (i : ℕ) :: env))
    (he : e < S.M + 1) (hb : b < S.M + 1) (ht : (e :: b :: (i : ℕ) :: env).getD t 0 = t') :
    RunZ S.W (wtTermE c t) (e :: b :: (i : ℕ) :: env)
      (if digitTest S.J t' i e then Lag.lagZ S.M e ⟨b, hb⟩ else 0) (Cost.wtTerm S.T) := by
  have hlag : RunZ S.W (Lag.lagE c.M c.B 0 1) (e :: b :: (i : ℕ) :: env) (Lag.lagZ S.M e ⟨b, hb⟩) (Cost.lag S.T) := by
    refine ⟨Lag.evalZ_lagE (e := 0) (b := 1) S.Sizes h.M h.B hb (Nat.lt_succ_iff.mp he), ?_⟩
    have := Lag.ops_lagE (B := c.B) (e := 0) (b := 1) S.Sizes h.M (env := e :: b :: (i : ℕ) :: env)
    have := S.M_le_T
    simp only [Cost.lag]
    omega
  have hN := S.M_le_T
  have hQ := S.Q_le_T
  have hi := i.2
  have hi1 : Run S.W (.add (.var 2) (.lit 1)) (e :: b :: (i : ℕ) :: env) ((i : ℕ) + 1) (1 + 1 + 1) :=
    Run.add (Run.var rfl) (Run.lit (one_lt_W S)) (S.small (by omega))
  have he1 : Run S.W (.add (.var 0) (.lit 1)) (e :: b :: (i : ℕ) :: env) (e + 1) (1 + 1 + 1) :=
    Run.add (Run.var rfl) (Run.lit (one_lt_W S)) (S.small (by omega))
  refine RunZ.ite hi1 (Run.var ht) (fun h1 => ?_) (fun h1 => ?_)
  · have hev : Run S.W (.var 0) (e :: b :: (i : ℕ) :: env) e 1 := Run.var rfl
    refine RunZ.ite (Run.var h.J) hev (fun h2 => hlag.eq (if_pos ?_).symm)
      (fun h2 => RunZ.lit0.eq (if_neg ?_).symm)
    · exact ⟨fun _ => h2, fun h3 => by omega⟩
    · exact fun h3 => h2 (h3.1 (by omega))
  · have hiv : Run S.W (.var 2) (e :: b :: (i : ℕ) :: env) (i : ℕ) 1 := Run.var rfl
    refine RunZ.ite hiv (Run.var ht) (fun h2 => ?_) (fun h2 => hlag.eq (if_pos ?_).symm)
    · refine RunZ.ite he1 (Run.var h.J) (fun h3 => hlag.eq (if_pos ?_).symm)
        (fun h3 => RunZ.lit0.eq (if_neg ?_).symm)
      · exact ⟨fun h4 => by omega, fun _ => by omega⟩
      · exact fun h4 => h3 (by have := h4.2 (by omega); omega)
    · exact ⟨fun h4 => by omega, fun h4 => by omega⟩

/-- The integer weight at the digit in variable `t` and the grid point in variable `p`: a product over the coordinates of sums over the
exponents. -/
def weightE (c : Ctx) (t p : ℕ) : Expr :=
  .prod (.var c.Q) (.letE (digE (p + 1) c.up.Nq 0)
    (.sum (.var c.up.up.Nq) (wtTermE c.up.up.up (t + 3))))

theorem run_powNq (h : Agree S c env) : Run S.W (powE c.Nq c.Q) env (S.Nq ^ S.Q) (2 + S.T * 2) :=
  Run.powE h.Nq h.Q S.Q_le_T (S.Nq_pow_lt le_rfl)

theorem runZ_weightE (h : Agree S c env) {t p P : ℕ} {t' : Fin S.Q} (ht : env.getD t 0 = t') (hp : env.getD p 0 = P) :
    RunZ S.W (weightE c t p) env (S.wZ t' (S.pOf P)) (Cost.wt S.T) := by
  classical
  unfold Setup.wZ Cost.wt
  refine RunZ.prodFin (B := Cost.wtBody S.T) (Run.var h.Q) S.Q_le_T fun i => ?_
  have hi := i.2
  have hup := h.up (i : ℕ)
  have h1 : Run S.W (digE (p + 1) c.up.Nq 0) ((i : ℕ) :: env) (dig S.Nq P i) (Cost.dig S.T) :=
    Run.digE hp hup.Nq rfl (hi.le.trans S.Q_le_T) (S.Nq_pow_lt hi.le)
  have hbl : dig S.Nq P i < S.M + 1 := dig_lt (Nat.succ_pos S.M) P i
  have hup2 := hup.up (dig S.Nq P i)
  have hNq : S.Nq ≤ S.T := by simp only [Setup.Nq, Setup.T]; omega
  refine RunZ.letE h1 ?_
  unfold Setup.wtZ digitSet
  rw [Finset.sum_filter]
  refine RunZ.sumFin (k := S.Nq) (B := Cost.wtTerm S.T) (Run.var hup2.Nq) hNq fun e => ?_
  exact runZ_wtTermE (t := t + 3) (hup2.up (e : ℕ)) e.2 hbl ht

/-! ### The next mask -/

/-- The value of `pop`. -/
def popNE (c : Ctx) (x : ℕ) : Expr := .sum (.var c.M) (bitX (x + 1) (.var 0))

theorem run_popNE (h : Agree S c env) {x X : ℕ} (hx : env.getD x 0 = X) (hX : X < 2 ^ S.M) :
    Run S.W (popNE c x) env (Enum.pop X) (Cost.popN S.T) := by
  have hNW : S.M < S.W := by have := S.M_le_T; have := S.T_lt_W; omega
  rw [Enum.pop_eq_sum hX]
  refine Run.sum (Run.var h.M) S.M_le_T (fun i hi => run_bitV hx rfl (by omega)) ?_
  rw [← Enum.pop_eq_sum hX]
  have : Enum.pop X ≤ S.M := by
    rw [Enum.pop_eq_sum hX]
    calc ∑ i ∈ range S.M, (X.testBit i).toNat ≤ ∑ _i ∈ range S.M, 1 :=
          Finset.sum_le_sum fun i _ => by cases X.testBit i <;> simp
      _ = S.M := by simp
  exact S.small ((this.trans S.M_le_T).trans (by omega))

/-- The value of `lowbit`, as a sum over the bits. -/
def lowE (c : Ctx) (x : ℕ) : Expr :=
  .sum (.var c.M) (.mul (.mul (bitX (x + 1) (.var 0))
    (.prod (.var 0) (.sub (.lit 1) (bitX (x + 2) (.var 0))))) (.pow2 (.var 0)))

theorem runZ_lowE (h : Agree S c env) {x X : ℕ} (hx : env.getD x 0 = X) (hX0 : 0 < X) (hX : X < 2 ^ S.M) :
    RunZ S.W (lowE c x) env (Enum.lowbit X : ℤ) (Cost.low S.T) := by
  have hNW : S.M < S.W := by have := S.M_le_T; have := S.T_lt_W; omega
  have hval : ((Enum.lowbit X : ℕ) : ℤ) = ∑ i ∈ range S.M,
      (((X.testBit i).toNat : ℤ) * (∏ j ∈ range i, (1 - ((X.testBit j).toNat : ℤ))) * ((2 ^ i : ℕ) : ℤ)) := by
    rw [Enum.lowbit_eq_sum hX0 hX]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    cases X.testBit j <;> simp
  rw [hval]
  refine RunZ.sum (B := Cost.lowBody S.T) (Run.var h.M) S.M_le_T fun i hi => ?_
  have hb : Run S.W (bitX (x + 1) (.var 0)) (i :: env) (X.testBit i).toNat Cost.bit := run_bitV hx rfl (by omega)
  have hp : Run S.W (.pow2 (.var 0)) (i :: env) (2 ^ i) (1 + 1) := Run.pow2 (Run.var rfl) (by omega)
  have hprod : RunZ S.W (.prod (.var 0) (.sub (.lit 1) (bitX (x + 2) (.var 0)))) (i :: env)
      (∏ j ∈ range i, (1 - ((X.testBit j).toNat : ℤ))) (1 + 1 + S.T * ((1 + 1 + Cost.bit) + 1)) := by
    refine RunZ.prod (Run.var rfl) (hi.le.trans S.M_le_T) fun j hj => ?_
    have hb2 : Run S.W (bitX (x + 2) (.var 0)) (j :: i :: env) (X.testBit j).toNat Cost.bit :=
      run_bitV hx rfl (by omega)
    exact RunZ.sub RunZ.lit1 hb2.toZ
  exact RunZ.mul (RunZ.mul hb.toZ hprod) hp.toZ

/-- The next mask of the variable `x`. -/
def nextE (c : Ctx) (x : ℕ) : Expr :=
  .ite (.pow2 (.var c.M)) (.var x) (.var x)
    (.ite (.add (popNE c x) (.lit 2)) (.var c.J) (.add (.var x) (.lit 1))
      (.ite (.var x) (.lit 0) (.pow2 (.var c.M)) (.add (.var x) (lowE c x))))

theorem run_nextE (h : Agree S c env) {x X : ℕ} (hx : env.getD x 0 = X) :
    Run S.W (nextE c x) env (progNext S.M S.J X) (Cost.next S.T) := by
  have hNW : S.M + 2 < S.W := by have := S.M_le_T; have := S.T_lt_W; omega
  have hp : Run S.W (.pow2 (.var c.M)) env (2 ^ S.M) (1 + 1) := Run.pow2 (Run.var h.M) (by omega)
  have hpw : 2 ^ (S.M + 1) < 2 ^ S.W := S.pow_lt_W (by omega)
  have h2N : 2 ^ (S.M + 1) = 2 * 2 ^ S.M := by rw [pow_succ]; ring
  have hN0 : 0 < 2 ^ S.M := by positivity
  refine (Run.ite (cc := 1) (cd := 1 + (1 + Cost.popN S.T + 1) + 1 + ((1 + 1 + 1) + (1 + 1 + 1 + ((1 + 1) + (1 + 1 + Cost.low S.T))))) hp (Run.var hx) (fun hle => (Run.var hx).eq ?_) (fun hle => ?_)).mono (by simp only [Cost.next]; omega)
  · rw [progNext, if_pos hle]
  · have hX : X < 2 ^ S.M := not_le.mp hle
    have hpop := run_popNE h hx hX
    have hpopN : Enum.pop X ≤ S.M := by
      rw [Enum.pop_eq_sum hX]
      calc ∑ i ∈ range S.M, (X.testBit i).toNat ≤ ∑ _i ∈ range S.M, 1 :=
            Finset.sum_le_sum fun i _ => by cases X.testBit i <;> simp
        _ = S.M := by simp
    have hadd : Run S.W (.add (popNE c x) (.lit 2)) env (Enum.pop X + 2) (1 + Cost.popN S.T + 1) :=
      Run.add hpop (Run.lit (S.small (by have := S.T_pos; omega))) (S.small (by have := S.M_le_T; omega))
    refine Run.ite hadd (Run.var h.J) (fun h1 => ?_) (fun h1 => ?_)
    · have := Run.add (Run.var hx) (Run.lit (one_lt_W S)) (x := X) (y := 1) (env := env) (by omega)
      refine this.eq ?_
      rw [progNext, if_neg hle, Enum.next, if_pos (by omega)]
    · refine Run.ite (Run.var hx) (Run.lit (by positivity)) (fun h2 => hp.eq ?_) (fun h2 => ?_)
      · have : X = 0 := by omega
        rw [progNext, if_neg hle, Enum.next, if_neg (by omega), if_pos this]
      · have hX0 : 0 < X := by omega
        have hlow := runZ_lowE h hx hX0 hX
        have hl := lowbit_lt hX0 hX
        have hz := RunZ.add (Run.var (W := S.W) hx).toZ hlow
        have hex : Run S.W (.add (.var x) (lowE c x)) env (X + Enum.lowbit X) (1 + 1 + Cost.low S.T) :=
          RunZ.exact_add (hz.eq (by push_cast; rfl)) (by omega)
        refine hex.eq ?_
        rw [progNext, if_neg hle, Enum.next, if_neg (by omega), if_neg (by omega)]

/-- The iterates of the program, against the iterates of `Enum.next`. -/
theorem iterate_next (h : Agree S c env) (k : ℕ) :
    (Enum.it S.M S.J k < 2 ^ S.M → iterate S.W (nextE c.up 0) 0 env k = Enum.it S.M S.J k) ∧
      (2 ^ S.M ≤ Enum.it S.M S.J k → 2 ^ S.M ≤ iterate S.W (nextE c.up 0) 0 env k) := by
  induction k with
  | zero =>
    have : (0 : ℕ) < 2 ^ S.M := by positivity
    simp [iterate, Enum.it_zero]
  | succ k ih =>
    have hstep : iterate S.W (nextE c.up 0) 0 env (k + 1) =
        progNext S.M S.J (iterate S.W (nextE c.up 0) 0 env k) :=
      (run_nextE (h.up _) rfl).1
    rw [Enum.it_succ, hstep]
    have hlt := Enum.lt_next S.M S.J (Enum.it S.M S.J k)
    by_cases hk : Enum.it S.M S.J k < 2 ^ S.M
    · rw [ih.1 hk, progNext, if_neg (not_le.mpr hk)]
      exact ⟨fun _ => rfl, id⟩
    · have hk' := ih.2 (not_lt.mp hk)
      rw [progNext, if_pos hk']
      refine ⟨fun h5 => by omega, fun _ => hk'⟩

/-! ### The test of the masks -/

/-- The number of the bits of the mask in variable `x` that are not bits of the mask in variable `y`. -/
def subE (c : Ctx) (x y : ℕ) : Expr :=
  .sum (.var c.M) (.ite (bitX (x + 1) (.var 0)) (bitX (y + 1) (.var 0)) (.lit 0) (.lit 1))

theorem run_subE (h : Agree S c env) {x y X Y : ℕ} (hx : env.getD x 0 = X) (hy : env.getD y 0 = Y) :
    Run S.W (subE c x y) env (∑ i ∈ range S.M, if (X.testBit i).toNat ≤ (Y.testBit i).toNat then 0 else 1)
      (Cost.subBits S.T) := by
  have hNW : S.M < S.W := by have := S.M_le_T; have := S.T_lt_W; omega
  have hle : (∑ i ∈ range S.M, if (X.testBit i).toNat ≤ (Y.testBit i).toNat then 0 else 1) ≤ S.M := by
    calc (∑ i ∈ range S.M, if (X.testBit i).toNat ≤ (Y.testBit i).toNat then 0 else 1) ≤ ∑ _i ∈ range S.M, 1 :=
          Finset.sum_le_sum fun i _ => by split_ifs <;> omega
      _ = S.M := by simp
  refine Run.sum (B := 1 + Cost.bit + Cost.bit + (1 + 1)) (Run.var h.M) S.M_le_T (fun i hi => ?_)
    (S.small ((hle.trans S.M_le_T).trans (by omega)))
  have h1 : Run S.W (bitX (x + 1) (.var 0)) (i :: env) (X.testBit i).toNat Cost.bit := run_bitV hx rfl (by omega)
  have h2 : Run S.W (bitX (y + 1) (.var 0)) (i :: env) (Y.testBit i).toNat Cost.bit := run_bitV hy rfl (by omega)
  exact Run.ite h1 h2 (fun hc => (Run.lit (by positivity)).eq (by rw [if_pos hc]))
    (fun hc => (Run.lit (one_lt_W S)).eq (by rw [if_neg hc]))

theorem sub_zero_iff (X Y : ℕ) :
    (∑ i ∈ range S.M, if (X.testBit i).toNat ≤ (Y.testBit i).toNat then 0 else 1) ≤ 0 ↔ S.setS X ⊆ S.setS Y := by
  rw [Nat.le_zero, Finset.sum_eq_zero_iff, S.setS_subset_iff]
  constructor
  · intro h i hi hx
    have h1 := h i (mem_range.mpr hi)
    by_contra hy
    have hy' : Y.testBit i = false := by simpa using hy
    rw [hx, hy'] at h1
    simp at h1
  · intro h i hi
    have hi' := mem_range.mp hi
    rw [if_pos]
    cases hq : X.testBit i
    · simp
    · rw [h i hi' hq]

/-- `(-1) ^ k`, for `k` in variable `k`. -/
def signE (k : ℕ) : Expr :=
  .ite (.mod (.var k) (.lit 2)) (.lit 0) (.lit 1) (.sub (.lit 0) (.lit 1))

theorem runZ_signE {k K' : ℕ} (hk : env.getD k 0 = K') : RunZ S.W (signE k) env ((-1) ^ K') Cost.signV := by
  have hc : Run S.W (.mod (.var k) (.lit 2)) env (K' % 2) (1 + 1 + 1) :=
    Run.mod (Run.var hk) (Run.lit (two_lt_W S))
  refine RunZ.ite hc (Run.lit (by positivity)) (fun hle => RunZ.lit1.eq ?_) (fun hle => (RunZ.sub RunZ.lit0 RunZ.lit1).eq ?_)
  · have hev : Even K' := Nat.even_iff.mpr (by omega)
    rw [hev.neg_one_pow]
  · have hod : Odd K' := Nat.odd_iff.mpr (by omega)
    rw [hod.neg_one_pow]
    norm_num

/-- The test of the masks with the sign. -/
def cTestE (l : Loc) : Expr :=
  .letE (popNE l.c l.mT)
    (.ite (.var 0) (.var l.c.up.r)
      (.ite (subE l.c.up (l.mU + 1) (l.mS + 1)) (.lit 0) (signE 0) (.lit 0))
      (.lit 0))

theorem runZ_cTestE (h : Frame S l V env) (hT : V.mT < 2 ^ S.M) :
    RunZ S.W (cTestE l) env (cTest S.r (S.setS V.mT) (S.setS V.mS) (S.setS V.mU)) (Cost.cTestV S.T) := by
  have hp := run_popNE h.ag h.mT hT
  rw [← S.card_setS hT] at hp
  have hup := h.up (S.setS V.mT).card
  have hs := run_subE hup.ag (x := l.mU + 1) (y := l.mS + 1) h.mU h.mS
  unfold cTest
  refine (RunZ.letE hp (RunZ.ite (Run.var rfl) (Run.var hup.ag.r) (fun h1 => ?_) (fun h1 => RunZ.lit0.eq ?_)))
  · refine RunZ.ite hs (Run.lit (by positivity)) (fun h2 => ?_) (fun h2 => RunZ.lit0.eq ?_)
    · rw [if_pos ⟨h1, (sub_zero_iff _ _).mp h2⟩]
      exact runZ_signE rfl
    · rw [if_neg (fun h3 => h2 ((sub_zero_iff _ _).mpr h3.2))]
  · rw [if_neg (fun h3 => h1 h3.1)]

end OnePigeonhole.Pseudo.Leaf
