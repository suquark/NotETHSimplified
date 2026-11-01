import UncrossingWires.Pseudo.Frame
import TransposeBase.Pseudo.Place

/-!
# The first level as a program
-/

namespace UncrossingWires.Pseudo

open Finset TransposeBase.Pseudo TransposeBase.Pseudo.Leaf TransposeBase.General

variable {m v : ℕ}

/-- The tables of the frame hold the network `N`. The node program `nodeG` has the frame at the given index. -/
structure BaseOK (W : ℕ) (f : Frm) (N : BaseNet m v) (K : ℕ) (nodeG : ℕ → Expr) (Unode : ℕ) : Prop where
  hm : f.m = m
  hv : f.v = v
  htail : ∀ e : Fin m, Place.fld f.fw f.tT e = N.tail e
  hhead : ∀ e : Fin m, Place.fld f.fw f.hT e = N.head e
  hpart : ∀ α : Fin v, Place.fld f.fw f.pT α = N.rOf α
  hr : ∀ α, N.rOf α < K
  hK : 0 < K
  hBd : Place.Bd W m v f.fw K
  hsc : f.sc = 2 * m
  hW : (K + 1) ^ 4 + 8 * f.sc + 8 < W
  hnode : ∀ {g : ℕ} {env : List ℕ}, f.At env g → ∀ (α : Fin v) (A a1 a2 : ℕ), A < 2 ^ (2 * m) →
    RunZ W (nodeG (g + 10))
      ((α : ℕ) :: A :: m :: v :: 0 :: f.fw :: f.tT :: f.hT :: a1 :: a2 :: env)
      (N.φ α (read N.tail N.head α (BaseNet.asgX m A) (BaseNet.asgY m A))) Unode

/-- The bound on the operations of `wt0E`. -/
def wt0Cost (m : ℕ) : ℕ := 200 * (m + 1)

namespace BaseSpec

/-! ### Tests of equality: only one branch runs -/

section Rules

variable {W : ℕ} {env : List ℕ} {a b c d : Expr} {x y r ca cb C : ℕ} {u : ℤ}

theorem eval_eqX (ha : Run W a env x ca) (hb : Run W b env y cb) :
    eval W (eqX a b c d) env = if x = y then eval W c env else eval W d env := by
  simp only [Leaf.eqX, eval, ha.1, hb.1]
  split_ifs <;> first | rfl | omega

theorem ops_eqX (ha : Run W a env x ca) (hb : Run W b env y cb) :
    ops W (eqX a b c d) env ≤ 2 + 2 * (ca + cb) + if x = y then ops W c env else ops W d env := by
  have h1 := ha.2
  have h2 := hb.2
  simp only [Leaf.eqX, ops, ha.1, hb.1]
  split_ifs <;> omega

theorem run_eqX (ha : Run W a env x ca) (hb : Run W b env y cb)
    (h1 : x = y → Run W c env r C) (h2 : x ≠ y → Run W d env r C) :
    Run W (eqX a b c d) env r (2 + 2 * (ca + cb) + C) := by
  have h3 := ops_eqX (c := c) (d := d) ha hb
  by_cases h : x = y
  · have h4 := h1 h
    rw [if_pos h] at h3
    have := h4.2
    exact ⟨by rw [eval_eqX ha hb, if_pos h, h4.1], by omega⟩
  · have h4 := h2 h
    rw [if_neg h] at h3
    have := h4.2
    exact ⟨by rw [eval_eqX ha hb, if_neg h, h4.1], by omega⟩

theorem runZ_eqX (ha : Run W a env x ca) (hb : Run W b env y cb)
    (h1 : x = y → RunZ W c env u C) (h2 : x ≠ y → RunZ W d env u C) :
    RunZ W (eqX a b c d) env u (2 + 2 * (ca + cb) + C) := by
  have h3 := ops_eqX (c := c) (d := d) ha hb
  by_cases h : x = y
  · have h4 := h1 h
    rw [if_pos h] at h3
    have := h4.2
    refine ⟨?_, by omega⟩
    simp only [evalZ, eval_eqX ha hb, if_pos h]
    exact h4.1
  · have h4 := h2 h
    rw [if_neg h] at h3
    have := h4.2
    refine ⟨?_, by omega⟩
    simp only [evalZ, eval_eqX ha hb, if_neg h]
    exact h4.1

end Rules

/-! ### The sizes -/

section Wires

variable {W : ℕ} {f : Frm} {N : BaseNet m v} {K Unode : ℕ} {nodeG : ℕ → Expr}

theorem W_big (h : BaseOK W f N K nodeG Unode) : 16 * m + 8 < W := by
  have h1 := h.hW
  have h2 := h.hsc
  generalize (K + 1) ^ 4 = A at h1
  omega

theorem lt_pow {W n : ℕ} (hn : n < W) : n < 2 ^ W := hn.trans Nat.lt_two_pow_self

theorem one_lt_pow (h : BaseOK W f N K nodeG Unode) : 1 < 2 ^ W :=
  lt_pow (by have := W_big h; omega)

theorem w0_le (N : BaseNet m v) (x y : ℕ) : N.w0 x y ≤ m := by
  unfold BaseNet.w0
  calc (∑ e ∈ range m, if N.joins e x y then 1 else 0)
      ≤ ∑ _e ∈ range m, 1 := sum_le_sum fun e _ => by split_ifs <;> omega
    _ = m := by simp

theorem rk_le (N : BaseNet m v) (e : ℕ) : N.rk e ≤ e := by
  unfold BaseNet.rk
  calc (∑ f ∈ range e, if N.joins f (N.tw e) (N.hw e) then 1 else 0)
      ≤ ∑ _f ∈ range e, 1 := sum_le_sum fun f _ => by split_ifs <;> omega
    _ = e := by simp

/-- The numbers on one word have at most `2 * m` bits in all. -/
theorem sum_w0_le (h : BaseOK W f N K nodeG Unode) {x y : ℕ} (hx : x < K) (hy : y ≤ K) :
    ∑ t ∈ range y, N.w0 x t ≤ 2 * m := by
  calc ∑ t ∈ range y, N.w0 x t
      ≤ ∑ t ∈ range K, N.w0 x t :=
        sum_le_sum_of_subset (range_subset_range.mpr hy)
    _ ≤ ∑ x' ∈ range K, ∑ t ∈ range K, N.w0 x' t :=
        single_le_sum (f := fun x' => ∑ t ∈ range K, N.w0 x' t) (fun _ _ => Nat.zero_le _) (mem_range.mpr hx)
    _ ≤ 2 * m := N.w0_total h.hr

/-! ### The words of the wires, and `w0` -/

theorem run_twE (h : BaseOK W f N K nodeG Unode) {g ie e : ℕ} {env : List ℕ} (hf : f.At env g)
    (hie : env.getD ie 0 = e) (he : e < m) : Run W (twE g ie) env (N.tw e) 19 := by
  have h1 : Place.fld f.fw f.tT e = N.tail ⟨e, he⟩ := h.htail ⟨e, he⟩
  refine ⟨?_, (Place.ops_endPartE _ _ _ _ _ _).le⟩
  rw [twE, Place.eval_endPartE h.hBd hf.tT hf.pT hie hf.fw he (by rw [h1]; exact (N.tail _).2),
    Place.ptN, h1, h.hpart, BaseNet.tw, dif_pos he]

theorem run_hwE (h : BaseOK W f N K nodeG Unode) {g ie e : ℕ} {env : List ℕ} (hf : f.At env g)
    (hie : env.getD ie 0 = e) (he : e < m) : Run W (hwE g ie) env (N.hw e) 19 := by
  have h1 : Place.fld f.fw f.hT e = N.head ⟨e, he⟩ := h.hhead ⟨e, he⟩
  refine ⟨?_, (Place.ops_endPartE _ _ _ _ _ _).le⟩
  rw [hwE, Place.eval_endPartE h.hBd hf.hT hf.pT hie hf.fw he (by rw [h1]; exact (N.head _).2),
    Place.ptN, h1, h.hpart, BaseNet.hw, dif_pos he]

theorem run_joinsE {W : ℕ} {env : List ℕ} (h1 : 1 < 2 ^ W) {itw ihw ix iy tw hw x y : ℕ}
    (htw : env.getD itw 0 = tw) (hhw : env.getD ihw 0 = hw) (hx : env.getD ix 0 = x)
    (hy : env.getD iy 0 = y) :
    Run W (joinsE itw ihw ix iy) env (if (tw = x ∧ hw = y) ∨ (tw = y ∧ hw = x) then 1 else 0) 25 := by
  have v1 : Run W (.var itw) env tw 1 := Run.var htw
  have v2 : Run W (.var ihw) env hw 1 := Run.var hhw
  have v3 : Run W (.var ix) env x 1 := Run.var hx
  have v4 : Run W (.var iy) env y 1 := Run.var hy
  have l0 : Run W (.lit 0) env 0 1 := Run.lit (by omega)
  have l1 : Run W (.lit 1) env 1 1 := Run.lit h1
  have inner : Run W (eqX (.var ihw) (.var ix) (.lit 1) (.lit 0)) env (if hw = x then 1 else 0) 7 :=
    run_eqX v2 v3 (fun e => l1.eq (if_pos e).symm) (fun e => l0.eq (if_neg e).symm)
  have mid : Run W (eqX (.var itw) (.var iy) (eqX (.var ihw) (.var ix) (.lit 1) (.lit 0)) (.lit 0)) env
      (if tw = y ∧ hw = x then 1 else 0) 13 :=
    run_eqX v1 v4 (C := 7) (fun e => inner.eq (by simp [e]))
      (fun e => (l0.eq (by simp [e])).mono (by omega))
  have top : Run W (joinsE itw ihw ix iy) env
      (if (tw = x ∧ hw = y) ∨ (tw = y ∧ hw = x) then 1 else 0) (2 + 2 * (1 + 1) + 19) :=
    run_eqX v1 v3 (C := 19)
      (fun e1 => (run_eqX v2 v4 (C := 13)
        (fun e2 => (l1.eq (by simp [e1, e2])).mono (by omega))
        (fun e2 => mid.eq (by simp [e1, e2]))).mono (by omega))
      (fun e1 => (mid.eq (by simp [e1])).mono (by omega))
  exact top.mono (by omega)

/-- The body of a loop over the wires. It tests whether the wire `e` joins `x` and `y`. -/
theorem run_joinBody (h : BaseOK W f N K nodeG Unode) {g i e ix iy x y : ℕ} {env : List ℕ}
    (hf : f.At env g) (hi : env.getD i 0 = e) (he : e < m) (hx : env.getD ix 0 = x)
    (hy : env.getD iy 0 = y) :
    Run W (.letE (twE g i) (.letE (hwE (g + 1) (i + 1)) (joinsE 1 0 (ix + 2) (iy + 2)))) env
      (if N.joins e x y then 1 else 0) 65 := by
  have e1 := run_twE h hf hi he
  have e2 : Run W (hwE (g + 1) (i + 1)) (N.tw e :: env) (N.hw e) 19 :=
    run_hwE h (hf.up _) (by simpa using hi) he
  have e3 : Run W (joinsE 1 0 (ix + 2) (iy + 2)) (N.hw e :: N.tw e :: env) _ 25 :=
    run_joinsE (one_lt_pow h) (x := x) (y := y) rfl rfl (by simpa using hx) (by simpa using hy)
  exact ((Run.letE e1 (Run.letE e2 e3)).eq (if_congr Iff.rfl rfl rfl)).mono (by omega)

/-- `wt0E` is the program of `BaseNet.w0`, for all words. -/
theorem run_wt0E (h : BaseOK W f N K nodeG Unode) {g ix iy x y : ℕ} {env : List ℕ} (hf : f.At env g)
    (hx : env.getD ix 0 = x) (hy : env.getD iy 0 = y) :
    Run W (wt0E g ix iy) env (N.w0 x y) (wt0Cost m) := by
  have hn : Run W (.var (g + 8)) env m 1 := Run.var (by rw [hf.m, h.hm])
  have hlt : N.w0 x y < 2 ^ W := lt_pow (by have := w0_le N x y; have := W_big h; omega)
  have hs : Run W (wt0E g ix iy) env (N.w0 x y) (1 + 1 + m * (65 + 1)) :=
    Run.sum (F := fun e => if N.joins e x y then 1 else 0) hn le_rfl
      (fun i hi => run_joinBody h (hf.up i) (i := 0) rfl hi (by simpa using hx) (by simpa using hy)) hlt
  exact hs.mono (by unfold wt0Cost; omega)

end Wires

end BaseSpec

/-- **The weights of the first level.** -/
theorem wt0_spec {W : ℕ} {f : Frm} {N : BaseNet m v} {K Unode : ℕ} {nodeG : ℕ → Expr}
    (h : BaseOK W f N K nodeG Unode) : WtSpec W f K wt0E N.w0 (wt0Cost m) :=
  fun hf hx hy _ _ => BaseSpec.run_wt0E h hf hx hy

/-- The bound on the operations of `word0E`. -/
def word0Cost (K m v Unode : ℕ) : ℕ := 5000 * (K + 1) * (m + 1) ^ 2 + (v + 1) * (Unode + 100)

namespace BaseSpec

section Word

variable {W : ℕ} {f : Frm} {N : BaseNet m v} {K Unode : ℕ} {nodeG : ℕ → Expr}

/-! ### The number of a wire, and the bit at its end -/

/-- The bound on the operations of `rkE`. -/
def rkCost (m : ℕ) : ℕ := 42 + m * 66

theorem run_rkE (h : BaseOK W f N K nodeG Unode) {g ie e : ℕ} {env : List ℕ} (hf : f.At env g)
    (hie : env.getD ie 0 = e) (he : e < m) : Run W (rkE g ie) env (N.rk e) (rkCost m) := by
  have e1 := run_twE h hf hie he
  have hf1 := hf.up (N.tw e)
  have e2 : Run W (hwE (g + 1) (ie + 1)) (N.tw e :: env) (N.hw e) 19 :=
    run_hwE h hf1 (by simpa using hie) he
  have hf2 := hf1.up (N.hw e)
  have hn : Run W (.var (ie + 2)) (N.hw e :: N.tw e :: env) e 1 := Run.var (by simpa using hie)
  have hlt : N.rk e < 2 ^ W := lt_pow (by have := rk_le N e; have := W_big h; omega)
  have hs : Run W (.sum (.var (ie + 2)) (.letE (twE (g + 3) 0) (.letE (hwE (g + 4) 1) (joinsE 1 0 4 3))))
      (N.hw e :: N.tw e :: env) (N.rk e) (1 + 1 + m * (65 + 1)) :=
    Run.sum (F := fun t => if N.joins t (N.tw e) (N.hw e) then 1 else 0) hn he.le
      (fun t ht => run_joinBody h (hf2.up t) (i := 0) (ix := 2) (iy := 1) rfl (ht.trans he) rfl rfl) hlt
  exact (Run.letE e1 (Run.letE e2 hs)).mono (by unfold rkCost; omega)

theorem run_offE (h : BaseOK W f N K nodeG Unode) {g ix iy x y : ℕ} {env : List ℕ} (hf : f.At env g)
    (hx : env.getD ix 0 = x) (hy : env.getD iy 0 = y) (hxK : x < K) (hyK : y ≤ K) :
    Run W (offE wt0E g ix iy) env (∑ t ∈ range y, N.w0 x t) (1 + 1 + K * (wt0Cost m + 1)) := by
  have hlt : ∑ t ∈ range y, N.w0 x t < 2 ^ W :=
    lt_pow (by have := sum_w0_le h hxK hyK; have := W_big h; omega)
  exact Run.sum (F := N.w0 x) (Run.var hy) hyK
    (fun t _ => run_wt0E h (hf.up t) (by simpa using hx) rfl) hlt

/-- The bound on the operations of `endBitE`. -/
def endCost (K m : ℕ) : ℕ :=
  1 + (1 + (1 + 1 + (1 + (1 + 1 + K * (wt0Cost m + 1)))) + (1 + wt0Cost m)) + (5 + rkCost m)

theorem run_endBitE (h : BaseOK W f N K nodeG Unode) {g ix iZ iy ie x Z y e : ℕ} {env : List ℕ}
    (hf : f.At env g) (hx : env.getD ix 0 = x) (hZ : env.getD iZ 0 = Z) (hy : env.getD iy 0 = y)
    (hie : env.getD ie 0 = e) (hxK : x < K) (hyK : y < K) (he : e < m) :
    Run W (endBitE g ix iZ iy ie) env ((viewL K (N.w0 x) Z y).testBit (N.rk e)).toNat (endCost K m) := by
  have hbig := W_big h
  have hoff := run_offE h hf hx hy hxK hyK.le
  have hoffle := sum_w0_le h hxK hyK.le
  have hwt := run_wt0E h hf hx hy
  have hwle := w0_le N x y
  have hfield := (Run.mod (Run.div (Run.var hZ) (Run.pow2 hoff (by omega))) (Run.pow2 hwt (by omega))).eq
    (y := viewL K (N.w0 x) Z y) (by rw [viewL, if_pos hyK])
  have hrk := run_rkE h (hf.up (viewL K (N.w0 x) Z y)) (ie := ie + 1) (by simpa using hie) he
  have hrkle := rk_le N e
  exact (Run.letE hfield (Run.bitX rfl hrk (by omega) (by omega))).mono (by unfold endCost; omega)

/-! ### The word of the node program -/

theorem toNat_mul_pow_lt {W : ℕ} (b : Bool) {e : ℕ} (he : e < W) : b.toNat * 2 ^ e < 2 ^ W :=
  calc b.toNat * 2 ^ e ≤ 1 * 2 ^ e := Nat.mul_le_mul_right _ (Bool.toNat_le b)
    _ = 2 ^ e := one_mul _
    _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) he

theorem run_aWordE (h : BaseOK W f N K nodeG Unode) {g ix iZ x Z : ℕ} {env : List ℕ} (hf : f.At env g)
    (hx : env.getD ix 0 = x) (hZ : env.getD iZ 0 = Z) (hxK : x < K) :
    Run W (aWordE g ix iZ) env (N.aWord x (viewL K (N.w0 x) Z))
      (1 + 1 + m * (61 + 2 * endCost K m + 1)) := by
  have hbig := W_big h
  have hlt : N.aWord x (viewL K (N.w0 x) Z) < 2 ^ W :=
    (N.aWord_lt x _).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hn : Run W (.var (g + 8)) env m 1 := Run.var (by rw [hf.m, h.hm])
  refine Run.sum (B := 61 + 2 * endCost K m) hn le_rfl (fun e he => ?_) hlt
  have hF := single_le_sum (s := range m) (f := fun e =>
    (if N.tw e = x then ((viewL K (N.w0 x) Z (N.hw e)).testBit (N.rk e)).toNat * 2 ^ e else 0) +
      (if N.hw e = x then ((viewL K (N.w0 x) Z (N.tw e)).testBit (N.rk e)).toNat * 2 ^ (m + e) else 0))
    (fun _ _ => Nat.zero_le _) (mem_range.mpr he)
  have hfe := hf.up e
  have e1 : Run W (twE (g + 1) 0) (e :: env) (N.tw e) 19 := run_twE h hfe rfl he
  have hf1 := hfe.up (N.tw e)
  have e2 : Run W (hwE (g + 2) 1) (N.tw e :: e :: env) (N.hw e) 19 := run_hwE h hf1 rfl he
  have hf2 := hf1.up (N.hw e)
  have htwK : N.tw e < K := (N.tw_val ⟨e, he⟩).trans_lt (h.hr _)
  have hhwK : N.hw e < K := (N.hw_val ⟨e, he⟩).trans_lt (h.hr _)
  have hx3 : (N.hw e :: N.tw e :: e :: env).getD (ix + 3) 0 = x := by simpa using hx
  have hZ3 : (N.hw e :: N.tw e :: e :: env).getD (iZ + 3) 0 = Z := by simpa using hZ
  have hm3 : (N.hw e :: N.tw e :: e :: env).getD (g + 3 + 8) 0 = m := by
    rw [show g + 3 + 8 = g + 1 + 1 + 1 + 8 from rfl, hf2.m, h.hm]
  have l0 : Run W (.lit 0) (N.hw e :: N.tw e :: e :: env) 0 1 := Run.lit (by positivity)
  have v0 : Run W (.var 0) (N.hw e :: N.tw e :: e :: env) (N.hw e) 1 := Run.var rfl
  have v1 : Run W (.var 1) (N.hw e :: N.tw e :: e :: env) (N.tw e) 1 := Run.var rfl
  have v2 : Run W (.var 2) (N.hw e :: N.tw e :: e :: env) e 1 := Run.var rfl
  have t1 : Run W (eqX (.var 1) (.var (ix + 3))
      (.mul (endBitE (g + 3) (ix + 3) (iZ + 3) 0 2) (.pow2 (.var 2))) (.lit 0))
      (N.hw e :: N.tw e :: e :: env)
      (if N.tw e = x then ((viewL K (N.w0 x) Z (N.hw e)).testBit (N.rk e)).toNat * 2 ^ e else 0)
      (2 + 2 * (1 + 1) + (1 + endCost K m + (1 + 1))) :=
    run_eqX v1 (Run.var hx3)
      (fun hc => (Run.mul (run_endBitE h hf2 hx3 hZ3 (y := N.hw e) rfl (e := e) rfl hxK hhwK he)
        (Run.pow2 v2 (by omega)) (toNat_mul_pow_lt _ (by omega))).eq (if_pos hc).symm)
      (fun hc => (l0.eq (if_neg hc).symm).mono (by omega))
  have t2 : Run W (eqX (.var 0) (.var (ix + 3))
      (.mul (endBitE (g + 3) (ix + 3) (iZ + 3) 1 2) (.pow2 (.add (.var (g + 3 + 8)) (.var 2)))) (.lit 0))
      (N.hw e :: N.tw e :: e :: env)
      (if N.hw e = x then ((viewL K (N.w0 x) Z (N.tw e)).testBit (N.rk e)).toNat * 2 ^ (m + e) else 0)
      (2 + 2 * (1 + 1) + (1 + endCost K m + (1 + (1 + 1 + 1)))) :=
    run_eqX v0 (Run.var hx3)
      (fun hc => (Run.mul (run_endBitE h hf2 hx3 hZ3 (y := N.tw e) rfl (e := e) rfl hxK htwK he)
        (Run.pow2 (Run.add (Run.var hm3) v2 (lt_pow (by omega))) (by omega))
        (toNat_mul_pow_lt _ (by omega))).eq (if_pos hc).symm)
      (fun hc => (l0.eq (if_neg hc).symm).mono (by omega))
  have hadd := Run.add t1 t2 (hF.trans_lt hlt)
  exact (Run.letE e1 (Run.letE e2 hadd)).mono (by omega)

/-! ### The node -/

/-- The environment of the node program, built by the eight `letE` of `word0E`. -/
theorem runZ_nodeChain (h : BaseOK W f N K nodeG Unode) {g : ℕ} {env : List ℕ} (hf : f.At env g)
    (α : Fin v) {A : ℕ} (hA : A < 2 ^ (2 * m)) :
    RunZ W
      (.letE (.var (g + 2 + 4)) <|
       .letE (.var (g + 3 + 5)) <|
       .letE (.var (g + 4 + 6)) <|
       .letE (.lit 0) <|
       .letE (.var (g + 6 + 7)) <|
       .letE (.var (g + 7 + 8)) <|
       .letE (.var 7) <|
       .letE (.var 7) <|
         nodeG (g + 10))
      ((α : ℕ) :: A :: env)
      (N.φ α (read N.tail N.head α (BaseNet.asgX m A) (BaseNet.asgY m A))) (16 + Unode) := by
  have hf2 : f.At ((α : ℕ) :: A :: env) (g + 2) := (hf.up A).up α
  have hf3 := hf2.up f.hT
  have hf4 := hf3.up f.tT
  have hf5 := hf4.up f.fw
  have hf6 := hf5.up 0
  have hf7 := hf6.up v
  have r9 := h.hnode hf α A α A hA
  have r8 := RunZ.letE (Run.var (W := W) (i := 7) (x := (α : ℕ))
    (env := A :: m :: v :: 0 :: f.fw :: f.tT :: f.hT :: (α : ℕ) :: A :: env) rfl) r9
  have r7 := RunZ.letE (Run.var (W := W) (i := 7) (x := A)
    (env := m :: v :: 0 :: f.fw :: f.tT :: f.hT :: (α : ℕ) :: A :: env) rfl) r8
  have r6 := RunZ.letE (Run.var (W := W) (i := g + 7 + 8) (x := m)
    (env := v :: 0 :: f.fw :: f.tT :: f.hT :: (α : ℕ) :: A :: env) (hf7.m.trans h.hm)) r7
  have r5 := RunZ.letE (Run.var (W := W) (i := g + 6 + 7) (x := v)
    (env := 0 :: f.fw :: f.tT :: f.hT :: (α : ℕ) :: A :: env) (hf6.v.trans h.hv)) r6
  have r4 := RunZ.letE (Run.lit (W := W) (x := 0)
    (env := f.fw :: f.tT :: f.hT :: (α : ℕ) :: A :: env) (by positivity)) r5
  have r3 := RunZ.letE (Run.var (W := W) (i := g + 4 + 6) (x := f.fw)
    (env := f.tT :: f.hT :: (α : ℕ) :: A :: env) hf4.fw) r4
  have r2 := RunZ.letE (Run.var (W := W) (i := g + 3 + 5) (x := f.tT)
    (env := f.hT :: (α : ℕ) :: A :: env) hf3.tT) r3
  have r1 := RunZ.letE (Run.var (W := W) (i := g + 2 + 4) (x := f.hT)
    (env := (α : ℕ) :: A :: env) hf2.hT) r2
  exact r1.mono (by omega)

theorem word0_cost_le (K m : ℕ) :
    1 + (1 + 1 + m * (61 + 2 * endCost K m + 1)) + 2 ≤ 5000 * (K + 1) * (m + 1) ^ 2 := by
  obtain ⟨P, hP⟩ : ∃ P, P = (K + 1) * (m + 1) := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.succ_le_of_lt (by positivity)
  have h1 : endCost K m ≤ 321 * P := by
    have e1 : K * (200 * (m + 1) + 1) = 200 * (K * m) + 201 * K := by ring
    have e2 : P = K * m + K + m + 1 := by rw [hP]; ring
    unfold endCost wt0Cost rkCost
    omega
  have h2 : m * (61 + 2 * endCost K m + 1) ≤ m * (704 * P) := Nat.mul_le_mul_left _ (by omega)
  have h3 : 5000 * (K + 1) * (m + 1) ^ 2 = 5000 * (m * P) + 5000 * P := by rw [hP]; ring
  have h4 : m * (704 * P) = 704 * (m * P) := by ring
  omega

end Word

end BaseSpec

/-- **The word functions of the first level.** -/
theorem word0_spec {W : ℕ} {f : Frm} {N : BaseNet m v} {K Unode : ℕ} {nodeG : ℕ → Expr}
    (h : BaseOK W f N K nodeG Unode) :
    WordSpec W f K (word0E nodeG) N.w0 N.F0 (word0Cost K m v Unode) := by
  intro g ix iZ x Z env hf hx hZ hxK _
  have hA := BaseSpec.run_aWordE h hf hx hZ hxK
  have hAlt := N.aWord_lt x (viewL K (N.w0 x) Z)
  have hf1 := hf.up (N.aWord x (viewL K (N.w0 x) Z))
  have hn : Run W (.var (g + 1 + 7)) (N.aWord x (viewL K (N.w0 x) Z) :: env) v 1 :=
    Run.var (by rw [hf1.v, h.hv])
  unfold word0E BaseNet.F0
  refine RunZ.mono (RunZ.letE hA (RunZ.prodFin hn le_rfl (B := 38 + Unode) fun α => ?_)) ?_
  · have hf2 : f.At ((α : ℕ) :: N.aWord x (viewL K (N.w0 x) Z) :: env) (g + 2) := hf1.up _
    have hfld : Run W (Place.fieldE (g + 2 + 3) 0 (g + 2 + 6))
        ((α : ℕ) :: N.aWord x (viewL K (N.w0 x) Z) :: env) (N.rOf α) 9 := by
      refine ⟨?_, (Place.ops_fieldE _ _ _ _ _).le⟩
      rw [Place.eval_fieldE (iv := (α : ℕ)) hf2.pT rfl hf2.fw (h.hBd.idx_lt (by have := α.2; omega))
        h.hBd.fw_lt, h.hpart]
    have hxv : Run W (.var (ix + 2)) ((α : ℕ) :: N.aWord x (viewL K (N.w0 x) Z) :: env) x 1 :=
      Run.var (by simpa using hx)
    exact (BaseSpec.runZ_eqX hfld hxv (C := 16 + Unode)
      (fun hc => (BaseSpec.runZ_nodeChain h hf α hAlt).eq (if_pos hc).symm)
      (fun hc => (RunZ.lit1.eq (if_neg hc).symm).mono (by omega))).mono (by omega)
  · have h1 := BaseSpec.word0_cost_le K m
    have h2 : (v + 1) * (Unode + 100) = v * (38 + Unode + 1) + (61 * v + Unode + 100) := by ring
    unfold word0Cost
    omega

end UncrossingWires.Pseudo
