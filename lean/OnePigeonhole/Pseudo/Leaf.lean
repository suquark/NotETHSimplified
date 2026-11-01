import OnePigeonhole.Pseudo.LeafTop

/-!
# The program for one network

`coreE m lt nodeE`: the sum of the network, multiplied by the common denominator of `net_int`.

* `coreE_eval`: its value in the ring of words.
* `coreE_ops`: its number of word operations.
* `cost_poly`: the factors `Cost.P1`, `Cost.P2` are polynomials in `T = K + h + 2 * M + v + 1`. The constants of `Cost.P2` depend on the number of
  exponent vectors of a side, which depends only on `m`.

The core environment is `S.core`, and the fields of `Setup` are the hypotheses on the table and the node program.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf

/-- The indices of the global values in the environment of the body of `coreE`. -/
def baseCtx (lt : Lits) : Ctx where
  Pw := 0
  Bx := 1
  Eb := 2
  two := 3
  J := 4
  r := 5
  Nq := 6
  B := 7
  K := 8
  L := 9
  Q := 10
  M := 11
  v := 12
  h := 13
  fw := 14
  tailT := 15
  headT := 16
  partT := 17
  layT := 18
  depth := 11
  lt := lt

/-- **The core program.** The global values are bound once, then come the nested loops. -/
def coreE (m : ℕ) (lt : Lits) (nodeE : Expr) : Expr :=
  .letE (.lit (m ^ 4)) <| .letE (.lit (6 * m ^ 4)) <|
  .letE (powE 0 1) <|
  .letE (.mul (.add (.var 3) (.lit 2)) (.add (.var 3) (.lit 2))) <|
  .letE (.add (.var 4) (.lit 1)) <|
  .letE (.div (.var 5) (.lit m)) <|
  .letE (.add (.mul (.lit 2) (.var 0)) (.lit 1)) <|
  .letE (.mul (.lit 2) (.var 7)) <|
  .letE (.add (.pow2 (.var 7)) (.lit 1)) <|
  .letE (powE 0 8) <|
  .letE (.pow2 (.pow2 (.var 9))) <|
  loopsE (clOf m) (baseCtx lt) nodeE

variable (S : Setup)

theorem small_T3 {x : ℕ} (hx : x ≤ (S.T + 2) ^ 3) : x < 2 ^ S.W :=
  S.lt_pow_W (lt_of_le_of_lt hx S.T3_lt_W)

/-- The environment of the body. -/
abbrev Setup.env11 (S : Setup) : List ℕ :=
  S.Pw :: S.Bx :: S.Eb :: S.two :: S.J :: S.r :: S.Nq :: S.B :: S.K :: S.L :: S.Q :: S.core

theorem agree_base : Agree S (baseCtx S.lt) S.env11 :=
  { M := rfl, v := rfl, h := rfl, fw := rfl, tailT := rfl, headT := rfl, partT := rfl, layT := rfl,
    Q := rfl, L := rfl, K := rfl, B := rfl, Nq := rfl, r := rfl, J := rfl, two := rfl, Eb := rfl, Bx := rfl, Pw := rfl,
    core := ⟨[S.Pw, S.Bx, S.Eb, S.two, S.J, S.r, S.Nq, S.B, S.K, S.L, S.Q], rfl, rfl⟩,
    lt := rfl }

theorem lets_le (T x : ℕ) :
    1 + 1 + (1 + 1 + (1 + (2 + T * 2) + (1 + (1 + (1 + 1 + 1) + (1 + 1 + 1)) + (1 + (1 + 1 + 1) +
      (1 + (1 + 1 + 1) + (1 + (1 + (1 + 1 + 1) + 1) + (1 + (1 + 1 + 1) + (1 + (1 + (1 + 1) + 1) +
        (1 + (2 + T * 2) + (1 + (1 + (1 + 1)) + x)))))))))) ≤
      Cost.lets T + x := by
  unfold Cost.lets Cost.hdr
  omega

/-- The program with its value and its cost. -/
theorem runZ_coreE :
    RunZ S.W (coreE S.m S.lt S.nodeE) S.core S.total
      (Cost.total S.T S.Bx S.Unode S.v (2 ^ (S.M / S.m)) S.L (S.Nq ^ S.Q) S.nS S.Q) := by
  have hTw := S.T_lt_W
  have hQW := S.Q_lt_W
  have hQT := S.Q_le_T
  have hNT := S.M_le_T
  have hone := one_lt_W S
  have hagree := agree_base S
  have hb : RunZ S.W (loopsE (clOf S.m) (baseCtx S.lt) S.nodeE) S.env11 S.total _ := runZ_loopsE hagree
  have htwo : (2 : ℕ) < 2 ^ S.W := two_lt_W S
  have r1 : Run S.W (.lit (S.m ^ 4)) S.core S.Q 1 := Run.lit (S.small (Nat.le_add_right_of_le hQT))
  have r2 : Run S.W (.lit (6 * S.m ^ 4)) (S.Q :: S.core) S.L 1 :=
    Run.lit (S.small (Nat.le_add_right_of_le S.L_le_T))
  have r3 : Run S.W (powE 0 1) (S.L :: S.Q :: S.core) S.K (2 + S.T * 2) :=
    Run.powE rfl rfl hQT (S.small (Nat.le_add_right_of_le S.K_le_T))
  have hN2 : Run S.W (.add (.var 3) (.lit 2)) (S.K :: S.L :: S.Q :: S.core) (S.M + 2) (1 + 1 + 1) :=
    Run.add (Run.var rfl) (Run.lit htwo) (S.small (by omega))
  have hBs : S.B ≤ (S.T + 2) ^ 3 := by
    calc S.B ≤ (S.T + 2) * (S.T + 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = (S.T + 2) * (S.T + 2) * 1 := by ring
      _ ≤ (S.T + 2) * (S.T + 2) * (S.T + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = (S.T + 2) ^ 3 := by ring
  have r4 : Run S.W (.mul (.add (.var 3) (.lit 2)) (.add (.var 3) (.lit 2))) (S.K :: S.L :: S.Q :: S.core) S.B
      (1 + (1 + 1 + 1) + (1 + 1 + 1)) :=
    Run.mul hN2 hN2 (small_T3 S hBs)
  have r5 : Run S.W (.add (.var 4) (.lit 1)) (S.B :: S.K :: S.L :: S.Q :: S.core) S.Nq (1 + 1 + 1) :=
    Run.add (Run.var rfl) (Run.lit hone) (S.small (by omega))
  have hmQ : S.m ≤ S.Q := Nat.le_self_pow (by norm_num) _
  have r6 : Run S.W (.div (.var 5) (.lit S.m)) (S.Nq :: S.B :: S.K :: S.L :: S.Q :: S.core) S.r (1 + 1 + 1) :=
    Run.div (Run.var rfl) (Run.lit (S.small (by omega)))
  have hJle : 2 * (S.M / S.m) + 1 ≤ S.M + 1 := small_J S
  have r7 : Run S.W (.add (.mul (.lit 2) (.var 0)) (.lit 1)) (S.r :: S.Nq :: S.B :: S.K :: S.L :: S.Q :: S.core) S.J
      (1 + (1 + 1 + 1) + 1) :=
    Run.add (Run.mul (Run.lit htwo) (Run.var rfl) (S.small (by omega))) (Run.lit hone) (S.small (by omega))
  have r8 : Run S.W (.mul (.lit 2) (.var 7)) (S.J :: S.r :: S.Nq :: S.B :: S.K :: S.L :: S.Q :: S.core) S.two (1 + 1 + 1) :=
    Run.mul (Run.lit htwo) (Run.var rfl) (S.small (Nat.le_add_right_of_le S.two_le_T))
  have r9 : Run S.W (.add (.pow2 (.var 7)) (.lit 1)) (S.two :: S.J :: S.r :: S.Nq :: S.B :: S.K :: S.L :: S.Q :: S.core)
      S.Eb (1 + (1 + 1) + 1) :=
    Run.add (Run.pow2 (Run.var rfl) hQW) (Run.lit hone) (S.small (by have := S.two_pow_Q_le_T; omega))
  have r10 : Run S.W (powE 0 8) (S.Eb :: S.two :: S.J :: S.r :: S.Nq :: S.B :: S.K :: S.L :: S.Q :: S.core) S.Bx
      (2 + S.T * 2) :=
    Run.powE rfl rfl hQT (S.lt_pow_W S.Bx_lt_W)
  have r11 : Run S.W (.pow2 (.pow2 (.var 9)))
      (S.Bx :: S.Eb :: S.two :: S.J :: S.r :: S.Nq :: S.B :: S.K :: S.L :: S.Q :: S.core) S.Pw (1 + (1 + 1)) :=
    Run.pow2 (Run.pow2 (Run.var rfl) hQW) S.two_pow_Q_lt_W
  have hfinal := RunZ.letE r1 <| RunZ.letE r2 <| RunZ.letE r3 <| RunZ.letE r4 <| RunZ.letE r5 <| RunZ.letE r6 <|
    RunZ.letE r7 <| RunZ.letE r8 <| RunZ.letE r9 <| RunZ.letE r10 <| RunZ.letE r11 hb
  unfold coreE
  exact hfinal.mono (lets_le _ _)

/-! ### The value -/

/-- The number of keys. -/
abbrev Setup.nKeys (S : Setup) : ℕ := (keys S.Q S.L S.h).card

/-- The value of the loops is the denominator times the network sum. -/
theorem total_eq :
    S.total = ((S.M.factorial ^ S.Q * S.lt.D ^ (2 * S.nKeys) : ℕ) : ℤ) *
      ∑ z : Fin S.M → Bool, ∏ α, S.φ α (fun e => z e.1) := by
  obtain ⟨h1, h2⟩ := hypotheses_of_numbers (M := S.M) S.m_pos S.hnum le_rfl
  exact (net_int S.hOn S.hlt.bd h1 h2 (S.M.factorial ^ S.Q) S.wZ (fun t p => by rw [S.wZ_cast]) S.φ).symm

/-- **The value of the core program.** The core environment holds the tables of the placement. -/
theorem coreE_eval :
    evalZ S.W (coreE S.m S.lt S.nodeE) S.core =
      ((((S.M.factorial ^ S.Q * S.lt.D ^ (2 * S.nKeys) : ℕ) : ℤ) *
        ∑ z : Fin S.M → Bool, ∏ α, S.φ α (fun e => z e.1) : ℤ) : ZMod (2 ^ S.W)) := by
  rw [← total_eq]
  exact (runZ_coreE S).1

/-! ### The cost -/

namespace Cost

/-- The cost of one assignment of the bits of a letter, without the node programs. -/
def P2 (T Bx : ℕ) : ℕ :=
  (1 + assign T + (1 + block T Bx + (1 + 1 + T * (2 + 2 * (partDig T + 1) + 2 + 1)))) + 1 + count T +
    3 * next T + hdr T + lets T + 60

end Cost

theorem iter_step {T nS B d Z : ℕ} (hnS : 1 ≤ nS) (h : B + (Cost.next T + d + 15) ≤ Z) :
    Cost.iter T nS B + d ≤ nS * Z := by
  have h1 := loop_step' (k := nS) (c := 7) (x := ((1 + (1 + 1) + 1) + (1 + B)) + Cost.next T) (d := d) (Z := Z) hnS
    (by omega)
  unfold Cost.iter
  omega

/-- The arithmetic of the bound. -/
theorem total_le {T Bx U v Y L YP nS Q : ℕ} (hT : v ≤ T) (hY : 1 ≤ Y) (hL : 1 ≤ L) (hYP : 1 ≤ YP) (hnS : 1 ≤ nS)
    (hQ : 1 ≤ Q) :
    Cost.total T Bx U v Y L YP nS Q ≤
      Q * (YP * (nS * (nS * (nS * (Cost.P1 T + L * (Y * (Cost.P2 T Bx + 2 * (U * (v + 1))))))))) := by
  have hv : v * ((2 + 2 * (Cost.partDig T + 1) + 2 * (U + 1)) + 1) ≤
      T * (2 + 2 * (Cost.partDig T + 1) + 2 + 1) + 2 * (U * (v + 1)) := by
    have h1 : v * ((2 + 2 * (Cost.partDig T + 1) + 2 * (U + 1)) + 1) =
        v * (2 + 2 * (Cost.partDig T + 1) + 2 + 1) + 2 * (U * v) := by ring
    have h2 := Nat.mul_le_mul_right (2 + 2 * (Cost.partDig T + 1) + 2 + 1) hT
    have h3 : 2 * (U * v) ≤ 2 * (U * (v + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    omega
  set Q2 := Cost.P2 T Bx + 2 * (U * (v + 1)) with hQ2
  set H := Cost.hdr T + Cost.lets T with hH
  set nx := Cost.next T with hnx
  -- the sum of one letter
  have hgs : Cost.groupSum T Bx U v Y + (3 * nx + H + 55) ≤ Y * Q2 := by
    have h1 := loop_step' (k := Y) (c := 1 + Cost.count T) (x := Cost.groupBody T Bx U v) (d := 3 * nx + H + 55)
      (Z := Q2) hY (by
        simp only [Cost.groupBody, Cost.term, hQ2, Cost.P2, hH, hnx]
        simp only [hnx] at *
        omega)
    unfold Cost.groupSum
    omega
  -- the body of the masks
  have hLs := loop_step' (k := L) (c := 1) (x := Cost.groupSum T Bx U v Y) (d := 3 * nx + H + 52)
    (Z := Y * Q2) hL (by omega)
  have hs : Cost.tBody T Bx U v Y L + (3 * nx + H + 50) ≤ Cost.P1 T + L * (Y * Q2) := by
    unfold Cost.tBody Cost.P1
    omega
  set Z := Cost.P1 T + L * (Y * Q2) with hZ
  -- the loops
  have i3 := iter_step (T := T) (B := Cost.tBody T Bx U v Y L) (d := 2 * nx + H + 35) (Z := Z) hnS
    (by rw [← hnx]; omega)
  have i2 := iter_step (T := T) (B := Cost.iter T nS (Cost.tBody T Bx U v Y L)) (d := nx + H + 20) (Z := nS * Z) hnS
    (by rw [← hnx]; omega)
  have i1 := iter_step (T := T) (B := Cost.iter T nS (Cost.iter T nS (Cost.tBody T Bx U v Y L)))
    (d := Cost.hdr T + (1 + Cost.lets T + 2) + 2) (Z := nS * (nS * Z)) hnS
    (by rw [← hnx]; omega)
  have y1 := loop_step' (k := YP) (c := Cost.hdr T)
    (x := Cost.iter T nS (Cost.iter T nS (Cost.iter T nS (Cost.tBody T Bx U v Y L))))
    (d := 1 + Cost.lets T + 2) (Z := nS * (nS * (nS * Z))) hYP (by omega)
  have t1 := loop_step' (k := Q) (c := 1) (x := Cost.pLoop T Bx U v Y L YP nS) (d := Cost.lets T)
    (Z := YP * (nS * (nS * (nS * Z)))) hQ (by unfold Cost.pLoop; omega)
  unfold Cost.total Cost.tLoop
  omega

/-- **The number of word operations of the core program.** -/
theorem coreE_ops :
    ops S.W (coreE S.m S.lt S.nodeE) S.core ≤
      S.Q * (S.Nq ^ S.Q * (S.nS * (S.nS * (S.nS *
        (Cost.P1 S.T + S.L * (2 ^ (S.M / S.m) *
          (Cost.P2 S.T S.Bx + 2 * (S.Unode * (S.v + 1))))))))) := by
  have h := (runZ_coreE S).2
  exact h.trans (total_le S.v_le_T Nat.one_le_two_pow S.L_pos (Nat.one_le_pow _ _ (Nat.succ_pos _))
    Nat.one_le_two_pow S.Q_pos)

/-! ### The factors are polynomials -/

theorem pb_dig : PolyB (fun T => Cost.dig T) := by
  unfold Cost.dig
  poly_step

theorem pb_swapBody : PolyB (fun T => Cost.swapBody T) := by
  have h_dig := pb_dig
  unfold Cost.swapBody
  poly_step

theorem pb_swap : PolyB (fun T => Cost.swap T) := by
  have h_swapBody := pb_swapBody
  unfold Cost.swap
  poly_step

theorem pb_word (cb : ℕ) : PolyB (fun T => Cost.word T cb) := by
  have h_swap := pb_swap
  unfold Cost.word
  poly_step

theorem pb_mono : PolyB (fun T => Cost.mono T) := by
  have h_dig := pb_dig
  unfold Cost.mono
  poly_step

theorem pb_sideSum (Bx : ℕ) : PolyB (fun T => Cost.sideSum T Bx) := by
  have h_mono := pb_mono
  unfold Cost.sideSum
  poly_step

theorem pb_side (Bx : ℕ) : PolyB (fun T => Cost.side T Bx) := by
  have h1 := pb_word 1
  have h2 := pb_word Cost.bit
  have h3 := pb_word Cost.xBody
  have h4 := pb_word Cost.yBody
  have h_sideSum := pb_sideSum Bx
  unfold Cost.side
  poly_step

theorem pb_ord : PolyB (fun T => Cost.ord T) := by
  have h_dig := pb_dig
  unfold Cost.ord
  poly_step

theorem pb_sideIf (Bx : ℕ) : PolyB (fun T => Cost.sideIf T Bx) := by
  have h_dig := pb_dig
  have h_side := pb_side Bx
  unfold Cost.sideIf
  poly_step

theorem pb_cellBody (Bx : ℕ) : PolyB (fun T => Cost.cellBody T Bx) := by
  have h_ord := pb_ord
  have h_sideIf := pb_sideIf Bx
  unfold Cost.cellBody
  poly_step

theorem pb_sides (Bx : ℕ) : PolyB (fun T => Cost.sides T Bx) := by
  have h_cellBody := pb_cellBody Bx
  unfold Cost.sides
  poly_step

theorem pb_partDig : PolyB (fun T => Cost.partDig T) := by
  have h_dig := pb_dig
  unfold Cost.partDig
  poly_step

theorem pb_tests : PolyB (fun T => Cost.tests T) := by
  have h_partDig := pb_partDig
  unfold Cost.tests
  poly_step

theorem pb_block (Bx : ℕ) : PolyB (fun T => Cost.block T Bx) := by
  have h_tests := pb_tests
  have h_sides := pb_sides Bx
  unfold Cost.block
  poly_step

theorem pb_group : PolyB (fun T => Cost.group T) := by
  have h_partDig := pb_partDig
  unfold Cost.group
  poly_step

theorem pb_countBody : PolyB (fun T => Cost.countBody T) := by
  have h_group := pb_group
  unfold Cost.countBody
  poly_step

theorem pb_count : PolyB (fun T => Cost.count T) := by
  have h_countBody := pb_countBody
  unfold Cost.count
  poly_step

theorem pb_assignBody : PolyB (fun T => Cost.assignBody T) := by
  have h_group := pb_group
  have h_count := pb_count
  unfold Cost.assignBody
  poly_step

theorem pb_assign : PolyB (fun T => Cost.assign T) := by
  have h_assignBody := pb_assignBody
  unfold Cost.assign
  poly_step

theorem pb_hdr : PolyB (fun T => Cost.hdr T) := by
  unfold Cost.hdr
  poly_step

theorem pb_lets : PolyB (fun T => Cost.lets T) := by
  have h_hdr := pb_hdr
  unfold Cost.lets
  poly_step

theorem pb_popN : PolyB (fun T => Cost.popN T) := by
  unfold Cost.popN
  poly_step

theorem pb_lowBody : PolyB (fun T => Cost.lowBody T) := by
  unfold Cost.lowBody
  poly_step

theorem pb_low : PolyB (fun T => Cost.low T) := by
  have h_lowBody := pb_lowBody
  unfold Cost.low
  poly_step

theorem pb_next : PolyB (fun T => Cost.next T) := by
  have h_popN := pb_popN
  have h_low := pb_low
  unfold Cost.next
  poly_step

theorem pb_P2 (Bx : ℕ) : PolyB (fun T => Cost.P2 T Bx) := by
  have h_block := pb_block Bx
  have h_partDig := pb_partDig
  have h_count := pb_count
  have h_assign := pb_assign
  have h_next := pb_next
  have h_hdr := pb_hdr
  have h_lets := pb_lets
  unfold Cost.P2
  poly_step

theorem pb_wtTerm : PolyB (fun T => Cost.wtTerm T) := by
  unfold Cost.wtTerm Cost.lag
  poly_step

theorem pb_wtBody : PolyB (fun T => Cost.wtBody T) := by
  have h_dig := pb_dig
  have h_wtTerm := pb_wtTerm
  unfold Cost.wtBody
  poly_step

theorem pb_wt : PolyB (fun T => Cost.wt T) := by
  have h_wtBody := pb_wtBody
  unfold Cost.wt
  poly_step

theorem pb_subBits : PolyB (fun T => Cost.subBits T) := by
  unfold Cost.subBits
  poly_step

theorem pb_cTestV : PolyB (fun T => Cost.cTestV T) := by
  have h_popN := pb_popN
  have h_subBits := pb_subBits
  unfold Cost.cTestV
  poly_step

theorem pb_P1 : PolyB (fun T => Cost.P1 T) := by
  have h_wt := pb_wt
  have h_cTestV := pb_cTestV
  unfold Cost.P1
  poly_step

/-- `Cost.P1`, `Cost.P2` are bounded by a monomial, for a fixed number of exponent vectors. -/
theorem cost_poly (Bx : ℕ) : ∃ Kc dc, ∀ T, 1 ≤ T → Cost.P1 T ≤ Kc * T ^ dc ∧ Cost.P2 T Bx ≤ Kc * T ^ dc := by
  obtain ⟨Kc, dc, h⟩ := pb_P1.add (pb_P2 Bx)
  refine ⟨Kc, dc, fun T hT => ?_⟩
  have : Cost.P1 T + Cost.P2 T Bx ≤ Kc * T ^ dc := h T hT
  exact ⟨by omega, by omega⟩

/-- **The cost with constants that depend on `m`.** For each `m` there are `Kc`, `dc` such that, with `T = K + h + 2 * M + v + 1` and
`nS = 2 ^ (clOf m * (M / m + 1))`, every core program with this `m` costs at most
`Q * (M + 1) ^ Q * nS ^ 3 * (Kc * T ^ dc + L * 2 ^ (M / m) * (Kc * T ^ dc + 2 * Unode * (v + 1)))`. -/
theorem coreE_ops_poly (m : ℕ) : ∃ Kc dc : ℕ, ∀ S : Setup, S.m = m →
    ops S.W (coreE S.m S.lt S.nodeE) S.core ≤
      S.Q * S.Nq ^ S.Q * S.nS ^ 3 *
        (Kc * S.T ^ dc +
          S.L * 2 ^ (S.M / S.m) * (Kc * S.T ^ dc + 2 * (S.Unode * (S.v + 1)))) := by
  obtain ⟨Kc, dc, h⟩ := cost_poly ((2 ^ m ^ 4 + 1) ^ m ^ 4)
  refine ⟨Kc, dc, fun S hS => (coreE_ops S).trans ?_⟩
  subst hS
  obtain ⟨h1, h2⟩ := h S.T S.T_pos
  have hmid : Cost.P1 S.T + S.L * (2 ^ (S.M / S.m) * (Cost.P2 S.T S.Bx + 2 * (S.Unode * (S.v + 1)))) ≤
      Kc * S.T ^ dc + S.L * 2 ^ (S.M / S.m) * (Kc * S.T ^ dc + 2 * (S.Unode * (S.v + 1))) := by
    rw [mul_assoc S.L]
    exact Nat.add_le_add h1
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right h2 _)))
  calc _ ≤ S.Q * (S.Nq ^ S.Q * (S.nS * (S.nS * (S.nS *
        (Kc * S.T ^ dc + S.L * 2 ^ (S.M / S.m) * (Kc * S.T ^ dc + 2 * (S.Unode * (S.v + 1)))))))) := by
        gcongr
    _ = _ := by
        ring

end OnePigeonhole.Pseudo.Leaf
