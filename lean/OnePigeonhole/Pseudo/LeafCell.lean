import OnePigeonhole.Pseudo.LeafSetup

/-!
# One corner of a cube

The sets of wires as masks, the numbers of the grid points and of the keys, the exchange on numbers, the wire at a corner, and the words
of `2 ^ Q` bits at the corners of a cube.

A key is given by two numbers `U`, `V` below `K` and a layer. The corner `a` of this key has the cell `corner k a`, and `Wires.key_F_iff_c_eq`
says that the wire at this corner is the wire with this cell. So `wordE` runs over the corners, computes the numbers of the two words of the
cell by `swapE`, and looks for the wire by a sum over the wires. Then `fullWord` of `IntSide.lean` is its value (`run_wordE`).
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf

namespace Setup

variable (S : Setup)

/-- The set of wires with the mask `x`. -/
def setS (x : ℕ) : Finset (Fin S.M) := setOfMask (Equiv.refl (Fin S.M)) x

theorem mem_setS {x : ℕ} {i : Fin S.M} : i ∈ S.setS x ↔ x.testBit i = true := by
  simp [setS]

/-- The grid point of the number `p`. -/
def pOf (p : ℕ) : Fin S.Q → Fin (S.M + 1) := wordOf (Nat.succ_pos S.M) S.Q p

/-- The values of the grid point of the number `p`. -/
def pN (p : ℕ) : Fin S.Q → ℕ := fun i => (S.pOf p i : ℕ)

/-- The exponent vector of the number `e`. -/
def eOf (e : ℕ) : Box S.Q := wordOf (Nat.succ_pos (2 ^ S.Q)) S.Q e

/-- The key with the words of the numbers `u`, `w` and the layer `l`. -/
def keyN (u w : ℕ) (l : Fin S.h) : Key S.Q S.L S.h :=
  (fun i => (wordOf S.L_pos S.Q u i, wordOf S.L_pos S.Q w i), l)

theorem wordIdx_wordOf {U : ℕ} (hU : U < S.K) : wordIdx (wordOf S.L_pos S.Q U) = U :=
  Code.wordIdx_wordOf S.L_pos hU

theorem card_setS {x : ℕ} (hx : x < 2 ^ S.M) : (S.setS x).card = Enum.pop x := by
  obtain ⟨S', rfl⟩ := Enum.exists_mask_eq hx
  rw [setS, setOfMask_mask_eq, Finset.card_map, Enum.pop_mask]

/-- The masks are subsets exactly when their bits are. -/
theorem setS_subset_iff {x y : ℕ} :
    S.setS x ⊆ S.setS y ↔ ∀ i < S.M, x.testBit i = true → y.testBit i = true := by
  constructor
  · intro h i hi hx
    exact S.mem_setS.mp (h (S.mem_setS.mpr hx : (⟨i, hi⟩ : Fin S.M) ∈ S.setS x))
  · intro h i hi
    exact S.mem_setS.mpr (h _ i.2 (S.mem_setS.mp hi))

end Setup

theorem one_lt_W (S : Setup) : 1 < 2 ^ S.W := S.small (by have := S.T_pos; omega)

theorem two_lt_W (S : Setup) : (2 : ℕ) < 2 ^ S.W := S.small (by have := S.T_pos; omega)

/-! ### Costs -/

namespace Cost

def field : ℕ := 12
def bit : ℕ := 10
def dig (T : ℕ) : ℕ := 6 + T * 2
def swapBody (T : ℕ) : ℕ := 1 + (1 + bit + 1 + (dig T + dig T)) + (2 + T * 2)
def swap (T : ℕ) : ℕ := 2 + T * (swapBody T + 1)
/-- The word of an end of a wire. -/
def wire : ℕ := 1 + field + field
/-- The test of the cell of a wire. -/
def onCell (cd : ℕ) : ℕ :=
  2 + 2 * (wire + 1) + 2 * ((2 + 2 * (wire + 1) + 2 * ((2 + 2 * (field + 1) + 2 * (cd + 1)) + 1)) + 1)
/-- The word of `2 ^ Q` bits at the corners of a cube. -/
def word (T cb : ℕ) : ℕ :=
  1 + (1 + 1) + T * ((1 + swap T + (1 + swap T + (1 + (1 + 1 + T * (onCell cb + 1)) + (1 + 1)))) + 1)

end Cost

variable {S : Setup} {c : Ctx} {env : List ℕ}

/-! ### Fields and bits -/

/-- Field `i` of the variable `x`, with the width from the context. -/
def fieldE (c : Ctx) (x i : ℕ) : Expr :=
  .mod (.div (.var x) (.pow2 (.mul (.var i) (.var c.fw)))) (.pow2 (.var c.fw))

theorem run_fieldE (h : Agree S c env) {x i X I : ℕ} (hx : env.getD x 0 = X) (hi : env.getD i 0 = I)
    (hI : I ≤ S.T) : Run S.W (fieldE c x i) env (fld S.fw X I) Cost.field := by
  have hb := S.fw_lt_W
  have h1 : I * S.fw ≤ (S.T + 2) * (S.fw + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : S.fw ≤ (S.T + 2) * (S.fw + 1) := by nlinarith
  exact (Run.mod (Run.div (Run.var hx) (Run.pow2 (Run.mul (Run.var hi) (Run.var h.fw)
    (S.lt_pow_W (by omega))) (by omega))) (Run.pow2 (Run.var h.fw) (by omega))).mono (by simp only [Cost.field]; omega)

theorem run_bitV {k i X I : ℕ} (hk : env.getD k 0 = X) (hi : env.getD i 0 = I) (hI : I < S.W) :
    Run S.W (bitX k (.var i)) env (X.testBit I).toNat Cost.bit :=
  (Run.bitX hk (Run.var hi) hI S.W_two).mono (by simp only [Cost.bit]; omega)

/-! ### The exchange on numbers -/

/-- The number with digit `i` from `w` if bit `i` of `E` is set, else from `u`. -/
def swapE (c : Ctx) (E u w : ℕ) : Expr :=
  .sum (.var c.Q) (.mul (.ite (bitX (E + 1) (.var 0)) (.lit 0)
    (digE (u + 1) c.up.L 0) (digE (w + 1) c.up.L 0)) (powE c.up.L 0))

theorem run_swapE (h : Agree S c env) {E u w Em : ℕ} {U V : Fin S.Q → Fin S.L} (hE : env.getD E 0 = Em)
    (hu : env.getD u 0 = wordIdx U) (hw : env.getD w 0 = wordIdx V) :
    Run S.W (swapE c E u w) env (wordIdx (fun i => if i ∈ setE S.Q Em then V i else U i)) (Cost.swap S.T) := by
  have hdig : ∀ {Z : Fin S.Q → Fin S.L} (i : Fin S.Q), dig S.L (wordIdx Z) i = Z i := by
    intro Z i
    have := congrFun (wordOf_wordIdx S.L_pos Z) i
    exact congrArg Fin.val this
  have hF : wordIdx (fun i => if i ∈ setE S.Q Em then V i else U i) =
      ∑ i ∈ range S.Q, (if Em.testBit i then dig S.L (wordIdx V) i else dig S.L (wordIdx U) i) * S.L ^ i := by
    rw [Finset.sum_range (fun i => (if Em.testBit i then dig S.L (wordIdx V) i else dig S.L (wordIdx U) i) * S.L ^ i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mem_setE, hdig]
    by_cases hb : Em.testBit i = true <;> simp [hb]
  have hlt : wordIdx (fun i => if i ∈ setE S.Q Em then V i else U i) < 2 ^ S.W :=
    S.small (((wordIdx_lt _).le.trans S.K_le_T).trans (by omega))
  rw [hF] at hlt ⊢
  refine Run.sum (B := Cost.swapBody S.T) (Run.var h.Q) S.Q_le_T (fun i hi => ?_) hlt
  have hup := h.up i
  have hiT : i ≤ S.T := hi.le.trans S.Q_le_T
  have hb : Run S.W (bitX (E + 1) (.var 0)) (i :: env) (Em.testBit i).toNat Cost.bit :=
    run_bitV hE rfl (by have := S.T_lt_W; omega)
  have hi0 : (i :: env).getD 0 0 = i := rfl
  have hd : ∀ {Z : ℕ} {z : ℕ}, env.getD z 0 = Z →
      Run S.W (digE (z + 1) c.up.L 0) (i :: env) (dig S.L Z i) (Cost.dig S.T) :=
    fun hz => Run.digE hz hup.L hi0 hiT (S.small_L_pow hi.le)
  have hite : Run S.W (.ite (bitX (E + 1) (.var 0)) (.lit 0) (digE (u + 1) c.up.L 0) (digE (w + 1) c.up.L 0))
      (i :: env) (if Em.testBit i then dig S.L (wordIdx V) i else dig S.L (wordIdx U) i)
      (1 + Cost.bit + 1 + (Cost.dig S.T + Cost.dig S.T)) :=
    Run.ite (x := (Em.testBit i).toNat) (y := 0) hb (Run.lit (by positivity))
      (fun hle => (hd hu).eq (by
        have : Em.testBit i = false := by
          cases hq : Em.testBit i
          · rfl
          · simp [hq] at hle
        simp [this]))
      (fun hle => (hd hw).eq (by
        have : Em.testBit i = true := by
          cases hq : Em.testBit i
          · simp [hq] at hle
          · rfl
        simp [this]))
  refine Run.mul hite (Run.powE hup.L hi0 hiT (S.small_L_pow hi.le)) ?_
  have h1 : (if Em.testBit i then dig S.L (wordIdx V) i else dig S.L (wordIdx U) i) < S.L := by
    split_ifs <;> exact dig_lt S.L_pos _ _
  have h2 : (if Em.testBit i then dig S.L (wordIdx V) i else dig S.L (wordIdx U) i) * S.L ^ i ≤ S.L ^ (i + 1) := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ h1.le
  exact S.small ((h2.trans ((S.L_pow_le hi).trans S.K_le_T)).trans (by omega))

/-! ### The wire at a cell -/

/-- The number of the word of the tail of the wire in variable `e`. -/
def twE (c : Ctx) (e : ℕ) : Expr := .letE (fieldE c c.tailT e) (fieldE c.up c.up.partT 0)

/-- The number of the word of the head of the wire in variable `e`. -/
def hwE (c : Ctx) (e : ℕ) : Expr := .letE (fieldE c c.headT e) (fieldE c.up c.up.partT 0)

theorem run_twE (h : Agree S c env) {e : ℕ} {i : Fin S.M} (he : env.getD e 0 = i) :
    Run S.W (twE c e) env (wordIdx (S.wi.tw i)) Cost.wire := by
  have h1 := run_fieldE h h.tailT he (i.2.le.trans S.M_le_T)
  rw [S.htail i] at h1
  have hup := h.up (S.tail i : ℕ)
  have h2 := run_fieldE hup hup.partT (i := 0) (I := S.tail i) rfl ((S.tail i).2.le.trans S.v_le_T)
  rw [S.hpart] at h2
  rw [S.hOn.tw_eq]
  exact Run.letE h1 h2

theorem run_hwE (h : Agree S c env) {e : ℕ} {i : Fin S.M} (he : env.getD e 0 = i) :
    Run S.W (hwE c e) env (wordIdx (S.wi.hw i)) Cost.wire := by
  have h1 := run_fieldE h h.headT he (i.2.le.trans S.M_le_T)
  rw [S.hhead i] at h1
  have hup := h.up (S.head i : ℕ)
  have h2 := run_fieldE hup hup.partT (i := 0) (I := S.head i) rfl ((S.head i).2.le.trans S.v_le_T)
  rw [S.hpart] at h2
  rw [S.hOn.hw_eq]
  exact Run.letE h1 h2

/-- `d` if the wire in variable `0` has the cell with the numbers in the variables `U`, `V`, `l`, and `0` if not. -/
def onCellE (c : Ctx) (U V l : ℕ) (d : Expr) : Expr :=
  eqX (twE c 0) (.var U)
    (eqX (hwE c 0) (.var V) (eqX (fieldE c c.layT 0) (.var l) d (.lit 0)) (.lit 0)) (.lit 0)

theorem run_onCellE (h : Agree S c env) {U V l : ℕ} {d : Expr} {z cd : ℕ} {i : Fin S.M}
    {ω : OnePigeonhole.LCell S.Q S.L S.h} (h0 : env.getD 0 0 = i) (hU : env.getD U 0 = wordIdx ω.1.1)
    (hV : env.getD V 0 = wordIdx ω.1.2) (hl : env.getD l 0 = ω.2) (hd : Run S.W d env z cd) :
    Run S.W (onCellE c U V l d) env (if S.wi.c i = ω then z else 0) (Cost.onCell cd) := by
  have l0 : Run S.W (.lit 0) env 0 1 := Run.lit (by positivity)
  have r1 := run_twE h h0
  have r2 := run_hwE h h0
  have r3 := run_fieldE h h.layT h0 (i.2.le.trans S.M_le_T)
  rw [S.hlay i] at r3
  have c1 := Run.eqX (r := if S.wi.lay i = ω.2 then z else 0) r3 (Run.var hl)
    (fun e => hd.eq (if_pos (Fin.ext e)).symm)
    (fun e => l0.eq (if_neg fun e2 => e (congrArg Fin.val e2)).symm)
  have c2 := Run.eqX (r := if S.wi.hw i = ω.1.2 then (if S.wi.lay i = ω.2 then z else 0) else 0) r2 (Run.var hV)
    (fun e => c1.eq (if_pos (wordIdx_inj S.L_pos e)).symm)
    (fun e => l0.eq (if_neg fun e2 => e (congrArg wordIdx e2)).symm)
  have c3 := Run.eqX (r := if S.wi.tw i = ω.1.1 then
      (if S.wi.hw i = ω.1.2 then (if S.wi.lay i = ω.2 then z else 0) else 0) else 0) r1 (Run.var hU)
    (fun e => c2.eq (if_pos (wordIdx_inj S.L_pos e)).symm)
    (fun e => l0.eq (if_neg fun e2 => e (congrArg wordIdx e2)).symm)
  refine (c3.eq ?_).mono ?_
  · have hiff : S.wi.c i = ω ↔ S.wi.tw i = ω.1.1 ∧ S.wi.hw i = ω.1.2 ∧ S.wi.lay i = ω.2 := by
      obtain ⟨⟨a, b⟩, c'⟩ := ω
      simp [Wires.c, Prod.mk.injEq, and_assoc]
    by_cases h1 : S.wi.tw i = ω.1.1
    · by_cases h2 : S.wi.hw i = ω.1.2
      · by_cases h3 : S.wi.lay i = ω.2
        · rw [if_pos h1, if_pos h2, if_pos h3, if_pos (hiff.mpr ⟨h1, h2, h3⟩)]
        · rw [if_pos h1, if_pos h2, if_neg h3, if_neg (fun e => h3 (hiff.mp e).2.2)]
      · rw [if_pos h1, if_neg h2, if_neg (fun e => h2 (hiff.mp e).2.1)]
    · rw [if_neg h1, if_neg (fun e => h1 (hiff.mp e).1)]
  · simp only [Cost.onCell]
    omega

/-- A sum of exact bodies over `Fin k`. -/
theorem run_sumFin {W k cn T B : ℕ} {n b : Expr} {F : Fin k → ℕ} (hn : Run W n env k cn) (hk : k ≤ T)
    (h : ∀ i : Fin k, Run W b ((i : ℕ) :: env) (F i) B) (hlt : ∑ i, F i < 2 ^ W) :
    Run W (.sum n b) env (∑ i, F i) (1 + cn + T * (B + 1)) := by
  rw [Code.sum_fin_eq_range] at hlt ⊢
  refine Run.sum hn hk (fun i hi => ?_) hlt
  simpa [hi] using h ⟨i, hi⟩

/-- Different wires have different cells, so the sum over the wires at a cell is one bit. -/
theorem sum_cell_toNat (W : Wires S.Q S.L S.h S.M) (ω : OnePigeonhole.LCell S.Q S.L S.h) (f : Fin S.M → Bool) :
    ∑ e, (if W.c e = ω then (f e).toNat else 0) = (decide (∃ e, W.c e = ω ∧ f e = true)).toNat := by
  by_cases hex : ∃ i0, W.c i0 = ω
  · obtain ⟨i0, h0⟩ := hex
    rw [Finset.sum_eq_single i0 (fun i _ hne => if_neg fun hc => hne (W.c_inj (hc.trans h0.symm)))
      (fun h1 => absurd (mem_univ i0) h1), if_pos h0]
    cases hf : f i0
    · have : ¬ ∃ e, W.c e = ω ∧ f e = true := by
        rintro ⟨e, hc, he⟩
        rw [W.c_inj (hc.trans h0.symm), hf] at he
        exact Bool.noConfusion he
      simp [this]
    · have : ∃ e, W.c e = ω ∧ f e = true := ⟨i0, h0, hf⟩
      simp [this]
  · rw [Finset.sum_eq_zero fun i _ => if_neg fun hc => hex ⟨i, hc⟩]
    have : ¬ ∃ e, W.c e = ω ∧ f e = true := fun ⟨e, hc, _⟩ => hex ⟨e, hc⟩
    simp [this]

/-! ### The words at the corners -/

/-- The word of the cube with the numbers in the variables `u`, `w`, `l`: a sum over the corners `i` of the bit of the corner at `2 ^ i`. For each
corner it computes the numbers of the two words of the cell, and the body runs at the wires of this cell. -/
def wordE (c : Ctx) (body : Expr) (u w l : ℕ) : Expr :=
  .sum (.pow2 (.var c.Q))
    (.letE (swapE c.up 0 (u + 1) (w + 1))
      (.letE (swapE c.up.up 1 (w + 2) (u + 2))
        (.mul (.sum (.var (c.M + 3)) (onCellE c.up.up.up.up 2 1 (l + 4) body)) (.pow2 (.var 2)))))

theorem run_wordE (h : Agree S c env) {body : Expr} {u w l U V cb : ℕ} {ℓ : Fin S.h} {f : Fin S.M → Bool}
    (hu : env.getD u 0 = U) (hw : env.getD w 0 = V) (hl : env.getD l 0 = ℓ) (hU : U < S.K) (hV : V < S.K)
    (hb : ∀ (e : Fin S.M) (V' U' i : ℕ), Run S.W body ((e : ℕ) :: V' :: U' :: i :: env) (f e).toNat cb) :
    Run S.W (wordE c body u w l) env (fullWord S.wi (S.keyN U V ℓ) f) (Cost.word S.T cb) := by
  set k := S.keyN U V ℓ with hk
  have hTW := S.T_lt_W
  have hQW : S.Q < S.W := by have := S.Q_le_T; omega
  have hCW : 2 ^ S.Q < S.W := by have := S.two_pow_Q_le_T; omega
  have hval : fullWord S.wi k f =
      ∑ i ∈ range (2 ^ S.Q), (decide (∃ e, S.wi.c e = corner k (setE S.Q i) ∧ f e = true)).toNat * 2 ^ i := by
    unfold fullWord
    rw [patWord_filter]
  have hsum := sum_bit_lt (2 ^ S.Q) (fun i => (decide (∃ e, S.wi.c e = corner k (setE S.Q i) ∧ f e = true)).toNat)
    (fun i => toNat_decide_le _)
  rw [hval]
  refine Run.sum (Run.pow2 (Run.var h.Q) hQW) S.two_pow_Q_le_T (fun i hi => ?_) (hsum.trans (S.pow_lt_W hCW))
  have hup := h.up i
  have hu' : (i :: env).getD (u + 1) 0 = wordIdx (wordOf S.L_pos S.Q U) := by
    show env.getD u 0 = _
    rw [hu, S.wordIdx_wordOf hU]
  have hw' : (i :: env).getD (w + 1) 0 = wordIdx (wordOf S.L_pos S.Q V) := by
    show env.getD w 0 = _
    rw [hw, S.wordIdx_wordOf hV]
  have r1 : Run S.W (swapE c.up 0 (u + 1) (w + 1)) (i :: env) (wordIdx (corner k (setE S.Q i)).1.1) (Cost.swap S.T) :=
    run_swapE hup rfl hu' hw'
  have hup2 := hup.up (wordIdx (corner k (setE S.Q i)).1.1)
  have r2 : Run S.W (swapE c.up.up 1 (w + 2) (u + 2))
      (wordIdx (corner k (setE S.Q i)).1.1 :: i :: env) (wordIdx (corner k (setE S.Q i)).1.2) (Cost.swap S.T) :=
    run_swapE hup2 (Em := i) rfl hw' hu'
  set U' := wordIdx (corner k (setE S.Q i)).1.1 with hU'
  set V' := wordIdx (corner k (setE S.Q i)).1.2 with hV'
  have hup3 := hup2.up V'
  have hin : Run S.W (.sum (.var (c.M + 3)) (onCellE c.up.up.up.up 2 1 (l + 4) body)) (V' :: U' :: i :: env)
      (∑ e, if S.wi.c e = corner k (setE S.Q i) then (f e).toNat else 0) (1 + 1 + S.T * (Cost.onCell cb + 1)) := by
    refine run_sumFin (Run.var hup3.M) S.M_le_T (fun e => ?_) ?_
    · have hup4 := hup3.up (e : ℕ)
      have hl4 : ((e : ℕ) :: V' :: U' :: i :: env).getD (l + 4) 0 = ((corner k (setE S.Q i)).2 : ℕ) := hl
      exact run_onCellE hup4 rfl rfl rfl hl4 (hb e V' U' i)
    · rw [sum_cell_toNat]
      exact lt_of_le_of_lt (toNat_decide_le _) (one_lt_W S)
  rw [sum_cell_toNat] at hin
  have hp : Run S.W (.pow2 (.var 2)) (V' :: U' :: i :: env) (2 ^ i) (1 + 1) :=
    Run.pow2 (Run.var rfl) (by omega)
  refine Run.letE r1 (Run.letE r2 (Run.mul hin hp ?_))
  have hle : (decide (∃ e, S.wi.c e = corner k (setE S.Q i) ∧ f e = true)).toNat * 2 ^ i ≤ 1 * 2 ^ i :=
    Nat.mul_le_mul_right _ (toNat_decide_le _)
  rw [one_mul] at hle
  exact lt_of_le_of_lt hle (S.pow_lt_W (by omega))

end OnePigeonhole.Pseudo.Leaf
