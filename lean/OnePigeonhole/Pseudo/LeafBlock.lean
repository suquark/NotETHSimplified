import OnePigeonhole.Pseudo.LeafRead

/-!
# One letter

The product over the keys as a product over two numbers and a layer, and the scaled function `blockZ` of a letter: the tests of the rows in
`S` with this letter, times the sides with this letter.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf

namespace Cost

/-- The digit of a part. -/
def partDig (T : ℕ) : ℕ := 1 + field + dig T
def ord (T : ℕ) : ℕ := 1 + 1 + T * ((1 + (1 + dig T + 1) + dig T + (1 + 1)) + 1)
def sideIf (T Bx : ℕ) : ℕ := 2 + 2 * (dig T + 1) + 2 * (side T Bx + 1)
def cellBody (T Bx : ℕ) : ℕ := 1 + ord T + 1 + ((1 + sideIf T Bx + sideIf T Bx) + 1)
/-- The product over two numbers and a layer. -/
def sides (T Bx : ℕ) : ℕ := 1 + 1 + T * ((1 + 1 + T * ((1 + 1 + T * (cellBody T Bx + 1)) + 1)) + 1)
/-- The tests of the rows in `S`. -/
def tests (T : ℕ) : ℕ :=
  1 + 1 + T * ((1 + bit + 1 + (1 + (2 + 2 * ((1 + field + partDig T) + 1) +
    2 * ((2 + 2 * (bit + bit) + 2 * (1 + 1)) + 1)))) + 1)
def block (T Bx : ℕ) : ℕ := 1 + tests T + sides T Bx

end Cost

variable {S : Setup} {c : Ctx} {env : List ℕ} {l : Loc} {V : LV S}

namespace Setup

variable (S : Setup)

/-- A product over the keys is a product over two numbers and a layer. -/
theorem prod_keys (f : Key S.Q S.L S.h → ℤ) :
    ∏ k ∈ keys S.Q S.L S.h, f k =
      ∏ u ∈ range S.K, ∏ w ∈ range S.K, ∏ l : Fin S.h,
        if IsKey (S.keyN u w l) then f (S.keyN u w l) else 1 := by
  classical
  have e1 : ∏ k ∈ keys S.Q S.L S.h, f k =
      ∏ a : Fin S.Q → Fin S.L × Fin S.L, ∏ l : Fin S.h, if IsKey (a, l) then f (a, l) else 1 := by
    rw [keys, Finset.prod_filter, Fintype.prod_prod_type]
  rw [e1, ← (Equiv.arrowProdEquivProdArrow (Fin S.Q) (fun _ => Fin S.L) (fun _ => Fin S.L)).symm.prod_comp,
    Fintype.prod_prod_type, prod_word S.L_pos]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [prod_word S.L_pos]
  rfl

theorem letter_keyN_true (u w : ℕ) (l : Fin S.h) (t : Fin S.Q) :
    ((letter (S.keyN u w l) t true : Fin S.L) : ℕ) = dig S.L w t := rfl

theorem letter_keyN_false (u w : ℕ) (l : Fin S.h) (t : Fin S.Q) :
    ((letter (S.keyN u w l) t false : Fin S.L) : ℕ) = dig S.L u t := rfl

/-- At most `K ^ 2 * h` keys. -/
theorem card_keys_le : (keys S.Q S.L S.h).card ≤ S.K ^ 2 * S.h :=
  le_trans (Nat.le_mul_of_pos_right _ (by positivity)) (card_keys_mul_le S.Q S.L S.h)

end Setup

/-! ### The digit of a part -/

/-- Digit `t` of the word of the node in variable `α`. -/
def partDigE (c : Ctx) (t α : ℕ) : Expr :=
  .letE (fieldE c c.partT α) (digE 0 c.up.L (t + 1))

theorem run_partDigE (h : Agree S c env) {t α : ℕ} {t' : Fin S.Q} {a : Fin S.v}
    (ht : env.getD t 0 = t') (ha : env.getD α 0 = a) :
    Run S.W (partDigE c t α) env (S.wd a t' : ℕ) (Cost.partDig S.T) := by
  have h1 := run_fieldE h h.partT ha (a.2.le.trans S.v_le_T)
  rw [S.hpart a] at h1
  have hup := h.up (wordIdx (S.wd a))
  have h2 : Run S.W (digE 0 c.up.L (t + 1)) (wordIdx (S.wd a) :: env) (dig S.L (wordIdx (S.wd a)) t') (Cost.dig S.T) :=
    Run.digE rfl hup.L ht (t'.2.le.trans S.Q_le_T) (S.small_L_pow t'.2.le)
  refine (Run.letE h1 h2).eq ?_
  have := congrFun (wordOf_wordIdx S.L_pos (S.wd a)) t'
  exact congrArg Fin.val this

/-! ### The keys -/

/-- The number of digits where the digit of the number in `u` is not below the digit of the number in `w`. -/
def ordE (c : Ctx) (u w : ℕ) : Expr :=
  .sum (.var c.Q) (.ite (.add (digE (u + 1) c.up.L 0) (.lit 1)) (digE (w + 1) c.up.L 0) (.lit 0) (.lit 1))

theorem run_ordE (h : Agree S c env) {u w U Vv : ℕ} (hu : env.getD u 0 = U) (hw : env.getD w 0 = Vv) :
    Run S.W (ordE c u w) env (∑ i ∈ range S.Q, if dig S.L U i + 1 ≤ dig S.L Vv i then 0 else 1) (Cost.ord S.T) := by
  have hle : (∑ i ∈ range S.Q, if dig S.L U i + 1 ≤ dig S.L Vv i then 0 else 1) ≤ S.Q := by
    calc (∑ i ∈ range S.Q, if dig S.L U i + 1 ≤ dig S.L Vv i then 0 else 1) ≤ ∑ _i ∈ range S.Q, 1 :=
          Finset.sum_le_sum fun i _ => by split_ifs <;> omega
      _ = S.Q := by simp
  refine Run.sum (B := 1 + (1 + Cost.dig S.T + 1) + Cost.dig S.T + (1 + 1)) (Run.var h.Q) S.Q_le_T (fun i hi => ?_)
    (S.small ((hle.trans S.Q_le_T).trans (by omega)))
  have hup := h.up i
  have hiT := hi.le.trans S.Q_le_T
  have h1 : Run S.W (digE (u + 1) c.up.L 0) (i :: env) (dig S.L U i) (Cost.dig S.T) :=
    Run.digE hu hup.L rfl hiT (S.small_L_pow hi.le)
  have h2 : Run S.W (digE (w + 1) c.up.L 0) (i :: env) (dig S.L Vv i) (Cost.dig S.T) :=
    Run.digE hw hup.L rfl hiT (S.small_L_pow hi.le)
  have hd : dig S.L U i < S.L := dig_lt S.L_pos _ _
  have h3 := Run.add h1 (Run.lit (env := i :: env) (one_lt_W S))
    (S.small (by have := S.L_le_T; omega))
  exact Run.ite h3 h2 (fun hc => (Run.lit (by positivity)).eq (by rw [if_pos hc]))
    (fun hc => (Run.lit (one_lt_W S)).eq (by rw [if_neg hc]))

theorem ord_zero_iff (U Vv : ℕ) (ℓ : Fin S.h) :
    (∑ i ∈ range S.Q, if dig S.L U i + 1 ≤ dig S.L Vv i then 0 else 1) ≤ 0 ↔ IsKey (S.keyN U Vv ℓ) := by
  rw [Nat.le_zero, Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have h1 := h i (mem_range.mpr i.2)
    by_contra hc
    have : ¬ dig S.L U i + 1 ≤ dig S.L Vv i := fun h2 => hc h2
    rw [if_neg this] at h1
    omega
  · intro h i hi
    have h1 : dig S.L U i + 1 ≤ dig S.L Vv i := h ⟨i, mem_range.mp hi⟩
    rw [if_pos h1]

/-! ### The tests of the rows in `S` -/

/-- The tests of the rows in `S` with the letter in the variable `gv`. -/
def testsE (l : Loc) (gv : ℕ) : Expr :=
  .prod (.var l.c.M)
    (.ite (bitX (l.mS + 1) (.var 0)) (.lit 0) (.lit 1)
      (eqX (.letE (fieldE l.c.up l.c.up.tailT 0) (partDigE l.c.up.up (l.t + 2) 0)) (.var (gv + 1))
        (eqX (bitX (l.as + 1) (.var 0)) (bitX (l.mU + 1) (.var 0)) (.lit 1) (.lit 0))
        (.lit 1)))

/-- A product over a filtered set is a product over all elements with two tests. -/
theorem prod_filter_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (Z : Finset ι) (p : ι → Prop) [DecidablePred p]
    (f : ι → ℤ) : ∏ i ∈ Z.filter p, f i = ∏ i, if i ∈ Z then (if p i then f i else 1) else 1 := by
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_filter]

theorem runZ_testsE (h : Frame S l V env) {gv : ℕ} {g : Fin S.L} (hg : env.getD gv 0 = g) :
    RunZ S.W (testsE l gv) env
      (∏ i ∈ (S.setS V.mS).filter (fun i => S.wi.tw i V.t = g),
        if asgX S.M V.A i = decide (i ∈ S.setS V.mU) then 1 else 0)
      (Cost.tests S.T) := by
  rw [prod_filter_mem]
  unfold Cost.tests
  refine RunZ.prodFin (Run.var h.ag.M) S.M_le_T fun e => ?_
  have hup := h.up (e : ℕ)
  have hW : (e : ℕ) < S.W := by have := e.2; have := S.M_le_T; have := S.T_lt_W; omega
  have b1 : Run S.W (bitX (l.mS + 1) (.var 0)) ((e : ℕ) :: env) (V.mS.testBit e).toNat Cost.bit := run_bitV h.mS rfl hW
  have b2 : Run S.W (bitX (l.as + 1) (.var 0)) ((e : ℕ) :: env) (V.A.testBit e).toNat Cost.bit := run_bitV h.as rfl hW
  have b3 : Run S.W (bitX (l.mU + 1) (.var 0)) ((e : ℕ) :: env) (V.mU.testBit e).toNat Cost.bit := run_bitV h.mU rfl hW
  have d1 := run_fieldE hup.ag (x := l.c.up.tailT) (i := 0) (I := e) hup.ag.tailT rfl (e.2.le.trans S.M_le_T)
  rw [S.htail e] at d1
  have hup2 := hup.up (S.tail e : ℕ)
  have d2 : Run S.W (partDigE l.c.up.up (l.t + 2) 0) ((S.tail e : ℕ) :: (e : ℕ) :: env) (S.wd (S.tail e) V.t : ℕ)
      (Cost.partDig S.T) := run_partDigE hup2.ag h.t rfl
  have d3 := Run.letE d1 d2
  have hgv : Run S.W (.var (gv + 1)) ((e : ℕ) :: env) g 1 := Run.var hg
  have hl1 := RunZ.lit1 (W := S.W) (env := (e : ℕ) :: env)
  have hl0 := RunZ.lit0 (W := S.W) (env := (e : ℕ) :: env)
  have e1 : ∀ {a b : Bool}, a.toNat = b.toNat ↔ a = b := by
    intro a b
    cases a <;> cases b <;> simp
  have hmem : decide (e ∈ S.setS V.mU) = V.mU.testBit e := by
    have := memB_setS (S := S) V.mU e
    exact e1.mp this
  have c1 : RunZ S.W (eqX (bitX (l.as + 1) (.var 0)) (bitX (l.mU + 1) (.var 0)) (.lit 1) (.lit 0)) ((e : ℕ) :: env)
      (if asgX S.M V.A e = decide (e ∈ S.setS V.mU) then 1 else 0)
      (2 + 2 * (Cost.bit + Cost.bit) + 2 * (1 + 1)) := by
    have hx : asgX S.M V.A e = V.A.testBit e := rfl
    refine RunZ.eqX b2 b3 (fun hq => hl1.eq ?_) (fun hq => hl0.eq ?_)
    · rw [hmem, hx, if_pos (e1.mp hq)]
    · rw [hmem, hx, if_neg (fun hq2 => hq (e1.mpr hq2))]
  have c2 := RunZ.eqX (u := if S.wi.tw e V.t = g then
      (if asgX S.M V.A e = decide (e ∈ S.setS V.mU) then 1 else 0) else 1) d3 hgv
    (fun hq => c1.eq (by
      rw [S.hOn.tw_eq, if_pos (Fin.ext hq)]))
    (fun hq => hl1.eq (by
      rw [S.hOn.tw_eq, if_neg (fun hq2 => hq (congrArg Fin.val hq2))]))
  refine (RunZ.ite (x := (V.mS.testBit e).toNat) (y := 0) b1 (Run.lit (by positivity)) (fun hle => hl1.eq ?_)
    (fun hle => c2.eq ?_)).mono ?_
  · have h4 : V.mS.testBit e = false := by
      cases hq : V.mS.testBit e
      · rfl
      · simp [hq] at hle
    have h5 : e ∉ S.setS V.mS := fun hq => by
      have := S.mem_setS.mp hq
      rw [h4] at this
      exact Bool.noConfusion this
    rw [if_neg h5]
  · have h4 : V.mS.testBit e = true := by
      cases hq : V.mS.testBit e
      · simp [hq] at hle
      · rfl
    rw [if_pos (S.mem_setS.mpr h4)]
  · omega

/-! ### The sides -/

/-- The sides with the letter in the variable `gv`: a product over two numbers and a layer, and the two sides. -/
def sidesE (l : Loc) (gv : ℕ) : Expr :=
  .prod (.var l.c.K) (.prod (.var (l.c.K + 1)) (.prod (.var (l.c.h + 2))
    (.ite (ordE l.c.up.up.up 2 1) (.lit 0)
      (.mul
        (eqX (digE 1 (l.c.L + 3) (l.t + 3)) (.var (gv + 3)) (sideE l.up.up.up 1 2 1 0) (.lit 1))
        (eqX (digE 2 (l.c.L + 3) (l.t + 3)) (.var (gv + 3)) (sideE l.up.up.up 0 2 1 0) (.lit 1)))
      (.lit 1))))

theorem runZ_sidesE (h : Frame S l V env) {gv : ℕ} {g : Fin S.L} (hg : env.getD gv 0 = g) :
    RunZ S.W (sidesE l gv) env
      (∏ k ∈ keys S.Q S.L S.h, ∏ b : Bool, if letter k V.t b = g then
        sideK S.lt.D S.R S.wi V.t (S.pN V.p) (S.setS V.mT) (S.setS V.mS) (S.setS V.mU) (asgX S.M V.A) (asgY S.M V.A) k b
        else 1)
      (Cost.sides S.T S.Bx) := by
  have ht := V.t.2
  rw [S.prod_keys]
  unfold Cost.sides
  refine RunZ.prod (Run.var h.ag.K) S.K_le_T fun u hu =>
    RunZ.prod (Run.var (h.up u).ag.K) S.K_le_T fun w hw =>
      RunZ.prodFin (Run.var ((h.up u).up w).ag.h) S.h_le_T fun ℓ => ?_
  have hF := ((h.up u).up w).up (ℓ : ℕ)
  have hup := hF.ag
  have ho := run_ordE hup (u := 2) (w := 1) (U := u) (Vv := w) rfl rfl
  have hgv : Run S.W (.var (gv + 3)) ((ℓ : ℕ) :: w :: u :: env) g 1 := Run.var hg
  have hL3 : ((ℓ : ℕ) :: w :: u :: env).getD (l.c.L + 3) 0 = S.L := h.ag.L
  have hdw : Run S.W (digE 1 (l.c.L + 3) (l.t + 3)) ((ℓ : ℕ) :: w :: u :: env) (dig S.L w V.t) (Cost.dig S.T) :=
    Run.digE rfl hL3 h.t (ht.le.trans S.Q_le_T) (S.small_L_pow ht.le)
  have hdu : Run S.W (digE 2 (l.c.L + 3) (l.t + 3)) ((ℓ : ℕ) :: w :: u :: env) (dig S.L u V.t) (Cost.dig S.T) :=
    Run.digE rfl hL3 h.t (ht.le.trans S.Q_le_T) (S.small_L_pow ht.le)
  have hs1 := runZ_sideE hF true (u := 2) (w := 1) (ll := 0) (U := u) (Vv := w) (ℓ := ℓ) rfl rfl rfl hu hw
  have hs0 := runZ_sideE hF false (u := 2) (w := 1) (ll := 0) (U := u) (Vv := w) (ℓ := ℓ) rfl rfl rfl hu hw
  have hl1 := RunZ.lit1 (W := S.W) (env := (ℓ : ℕ) :: w :: u :: env)
  refine RunZ.ite ho (Run.lit (by positivity)) (fun hle => ?_) (fun hle => hl1.eq ?_)
  · rw [if_pos ((ord_zero_iff u w ℓ).mp hle), Fintype.prod_bool]
    refine RunZ.mul ?_ ?_
    · refine RunZ.eqX hdw hgv (fun e1 => hs1.eq ?_) (fun e1 => hl1.eq ?_)
      · rw [if_pos (Fin.ext e1)]
      · rw [if_neg (fun e2 => e1 (congrArg Fin.val e2))]
    · refine RunZ.eqX hdu hgv (fun e1 => hs0.eq ?_) (fun e1 => hl1.eq ?_)
      · rw [if_pos (Fin.ext e1)]
      · rw [if_neg (fun e2 => e1 (congrArg Fin.val e2))]
  · rw [if_neg (fun hc => hle ((ord_zero_iff u w ℓ).mpr hc))]

/-! ### The letter -/

/-- The scaled function of the letter in the variable `gv`. -/
def blockE (l : Loc) (gv : ℕ) : Expr := .mul (testsE l gv) (sidesE l gv)

theorem runZ_blockE (h : Frame S l V env) {gv : ℕ} {g : Fin S.L} (hg : env.getD gv 0 = g) :
    RunZ S.W (blockE l gv) env
      (blockZ S.lt.D S.R S.wi V.t (S.pN V.p) (S.setS V.mT) (S.setS V.mS) (S.setS V.mU) g (asgX S.M V.A) (asgY S.M V.A))
      (Cost.block S.T S.Bx) :=
  RunZ.mul (runZ_testsE h hg) (runZ_sidesE h hg)

end OnePigeonhole.Pseudo.Leaf
