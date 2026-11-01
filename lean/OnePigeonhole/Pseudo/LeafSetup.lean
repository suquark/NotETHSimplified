import OnePigeonhole.Pseudo.Helpers
import OnePigeonhole.Pseudo.IntSide

/-!
# The data of the core program

`Lits`: the literal table, which depends only on `m`. `Setup`: one network, its wires on the words of its nodes, the tables of the
network and of the placement, the node program and the word length. `Ctx`, `Agree`: where the global values live in the environment.

The numbers are those of Section 1 of `papers/one-pigeonhole/proof.tex`: `Q = m ^ 4`, `R = m ^ 3`, `L = 6 * Q`, `K = L ^ Q`. With `M` wires, the
numbers of the masks are `r = M / m` and `J = 2 * r + 1`.
-/

set_option linter.unusedSectionVars false

namespace OnePigeonhole.Pseudo.Leaf

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf

/-! ### The table -/

/-- The literal table: the scale `D`, the offset `off`, the field width `f`, and the packed table. -/
structure Lits where
  D : ℕ
  off : ℕ
  f : ℕ
  sT : ℕ

/-- The number of words of `2 ^ Q` bits. -/
abbrev pwN (Q : ℕ) : ℕ := 2 ^ 2 ^ Q

/-- The row of the table: the digit, the side, and the five words of the corners. -/
def sBase (Q t b Dw PTw PSw xw yw : ℕ) : ℕ :=
  pk (pwN Q) (pk (pwN Q) (pk (pwN Q) (pk (pwN Q) (pk (pwN Q) (pk 2 t b) Dw) PTw) PSw) xw) yw

/-- The position in the table of an exponent vector of a row. -/
def sIdx (Q t b Dw PTw PSw xw yw e : ℕ) : ℕ := pk (boxN Q) (sBase Q t b Dw PTw PSw xw yw) e

/-- The number of rows of the table. -/
def sRows (Q : ℕ) : ℕ := Q * 2 * pwN Q * pwN Q * pwN Q * pwN Q * pwN Q

/-- The size of the table. -/
def sSize (Q : ℕ) : ℕ := sRows Q * boxN Q

theorem sBase_lt {Q t b Dw PTw PSw xw yw : ℕ} (ht : t < Q) (hb : b < 2) (h1 : Dw < pwN Q) (h2 : PTw < pwN Q)
    (h3 : PSw < pwN Q) (h4 : xw < pwN Q) (h5 : yw < pwN Q) :
    sBase Q t b Dw PTw PSw xw yw < sRows Q := by
  unfold sBase sRows
  exact pk_lt (pk_lt (pk_lt (pk_lt (pk_lt (pk_lt ht hb) h1) h2) h3) h4) h5

theorem sIdx_lt {Q t b Dw PTw PSw xw yw e : ℕ} (ht : t < Q) (hb : b < 2) (h1 : Dw < pwN Q) (h2 : PTw < pwN Q)
    (h3 : PSw < pwN Q) (h4 : xw < pwN Q) (h5 : yw < pwN Q) (he : e < boxN Q) :
    sIdx Q t b Dw PTw PSw xw yw e < sSize Q :=
  pk_lt (sBase_lt ht hb h1 h2 h3 h4 h5) he

/-- The literal table holds the scaled coefficients of the sides. -/
structure Lits.Good (m : ℕ) (lt : Lits) : Prop where
  D_pos : 0 < lt.D
  coef : ∀ (t : Fin (m ^ 4)) (b : Bool) (Dw PTw PSw xw yw : ℕ),
    Dw < pwN (m ^ 4) → PTw < pwN (m ^ 4) → PSw < pwN (m ^ 4) → xw < pwN (m ^ 4) → yw < pwN (m ^ 4) →
    ∀ e : Box (m ^ 4),
    ((fld lt.f lt.sT (sIdx (m ^ 4) t b.toNat Dw PTw PSw xw yw (wordIdx e)) : ℕ) : ℤ) - lt.off =
      coefZ lt.D (m ^ 3) t Dw b PTw PSw xw yw e
  bd : SideScaled lt.D (m ^ 3) (m ^ 4)
  sT_lt : lt.sT < 2 ^ (lt.f * sSize (m ^ 4))

/-- The size of the literal table. -/
def Lits.wid (m : ℕ) (lt : Lits) : ℕ :=
  lt.f * sSize (m ^ 4) + lt.f + sSize (m ^ 4) + 2 * m ^ 4 + 2

/-- The word length is large enough. -/
structure Big (m h M v fw W : ℕ) (lt : Lits) : Prop where
  hT : ((6 * m ^ 4) ^ m ^ 4 + h + 2 * M + v + 3) ^ 3 < W
  hQ : (m ^ 4 + 3) * ((6 * m ^ 4) ^ m ^ 4 + h + 2 * M + v + 3) < W
  hcl : clOf m * ((6 * m ^ 4) ^ m ^ 4 + h + 2 * M + v + 3) < W
  hfw : ((6 * m ^ 4) ^ m ^ 4 + h + 2 * M + v + 3) * (fw + 1) < W
  hlit : Lits.wid m lt < W

/-- One network with its wires and its tables. -/
structure Setup where
  m : ℕ
  M : ℕ
  v : ℕ
  h : ℕ
  fw : ℕ
  W : ℕ
  hm : 40 ≤ m
  lt : Lits
  hlt : lt.Good m
  tail : Fin M → Fin v
  head : Fin M → Fin v
  wd : Fin v → Fin (m ^ 4) → Fin (6 * m ^ 4)
  wi : Wires (m ^ 4) (6 * m ^ 4) h M
  hOn : OnNodes wi tail head wd
  hnum : 2 * (((6 * m ^ 4) ^ m ^ 4) ^ 2 * h) ≤ m * M
  tailT : ℕ
  headT : ℕ
  partT : ℕ
  layT : ℕ
  outer : List ℕ
  htail : ∀ e : Fin M, fld fw tailT e = tail e
  hhead : ∀ e : Fin M, fld fw headT e = head e
  hpart : ∀ α : Fin v, fld fw partT α = wordIdx (wd α)
  hlay : ∀ e : Fin M, fld fw layT e = wi.lay e
  φ : (α : Fin v) → (Inc tail head α → Bool) → ℤ
  nodeE : Expr
  Unode : ℕ
  hnode : ∀ (α : Fin v) (A : ℕ), A < 2 ^ (2 * M) →
    RunZ W nodeE ((α : ℕ) :: A :: M :: v :: h :: fw :: tailT :: headT :: partT :: layT :: outer)
      (φ α (read tail head α (asgX M A) (asgY M A))) Unode
  big : Big m h M v fw W lt

namespace Setup

variable (S : Setup)

abbrev Q : ℕ := S.m ^ 4
abbrev R : ℕ := S.m ^ 3
abbrev L : ℕ := 6 * S.m ^ 4
abbrev K : ℕ := S.L ^ S.Q
abbrev Nq : ℕ := S.M + 1
abbrev B : ℕ := (S.M + 2) * (S.M + 2)
abbrev r : ℕ := S.M / S.m
abbrev J : ℕ := 2 * (S.M / S.m) + 1
abbrev two : ℕ := 2 * S.M
abbrev T : ℕ := S.K + S.h + 2 * S.M + S.v + 1
abbrev Eb : ℕ := 2 ^ S.Q + 1
abbrev Bx : ℕ := S.Eb ^ S.Q
abbrev Pw : ℕ := 2 ^ 2 ^ S.Q

/-- The environment of the core program. -/
abbrev core : List ℕ :=
  S.M :: S.v :: S.h :: S.fw :: S.tailT :: S.headT :: S.partT :: S.layT :: S.outer

theorem m_pos : 0 < S.m := by have := S.hm; omega

theorem m_two : 2 ≤ S.m := by have := S.hm; omega

theorem Q_pos : 0 < S.Q := pow_pos S.m_pos _

theorem L_two : 2 ≤ S.L := by have := S.Q_pos; simp only [L, Q] at *; omega

theorem L_pos : 0 < S.L := by have := S.L_two; omega

theorem K_pos : 0 < S.K := pow_pos S.L_pos _

theorem two_pow_le_K : 2 ^ S.Q ≤ S.K := Nat.pow_le_pow_left S.L_two _

theorem Q_lt_two_pow : S.Q < 2 ^ S.Q := Nat.lt_two_pow_self

theorem Q_le_K : S.Q ≤ S.K := S.Q_lt_two_pow.le.trans S.two_pow_le_K

theorem L_le_K : S.L ≤ S.K := by
  calc S.L = S.L ^ 1 := by simp
    _ ≤ S.L ^ S.Q := Nat.pow_le_pow_right S.L_pos S.Q_pos

theorem L_pow_le {i : ℕ} (hi : i ≤ S.Q) : S.L ^ i ≤ S.K := Nat.pow_le_pow_right S.L_pos hi

theorem K_le_T : S.K ≤ S.T := by simp only [T]; omega

theorem h_le_T : S.h ≤ S.T := by simp only [T]; omega

theorem two_le_T : S.two ≤ S.T := by simp only [T, two]; omega

theorem M_le_T : S.M ≤ S.T := by simp only [T]; omega

theorem v_le_T : S.v ≤ S.T := by simp only [T]; omega

theorem T_pos : 1 ≤ S.T := by simp only [T]; omega

theorem T_ge_two : 2 ≤ S.T := by have := S.K_pos; simp only [T]; omega

theorem Q_le_T : S.Q ≤ S.T := S.Q_le_K.trans S.K_le_T

theorem L_le_T : S.L ≤ S.T := S.L_le_K.trans S.K_le_T

theorem two_pow_Q_le_T : 2 ^ S.Q ≤ S.T := S.two_pow_le_K.trans S.K_le_T

theorem T3_lt_W : (S.T + 2) ^ 3 < S.W := S.big.hT

theorem T_lt_W : S.T + 2 < S.W := by
  have h := S.T3_lt_W
  have h2 : S.T + 2 ≤ (S.T + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem QT_lt_W : (S.Q + 3) * (S.T + 2) < S.W := S.big.hQ

theorem fw_lt_W : (S.T + 2) * (S.fw + 1) < S.W := S.big.hfw

theorem W_two : 2 ≤ S.W := by have := S.T_lt_W; omega

theorem lt_pow_W {x : ℕ} (hx : x < S.W) : x < 2 ^ S.W := hx.trans Nat.lt_two_pow_self

/-- Anything below the word length fits in a word. -/
theorem small {x : ℕ} (hx : x ≤ S.T + 2) : x < 2 ^ S.W :=
  S.lt_pow_W (by have := S.T_lt_W; omega)

theorem pow_lt_W {x : ℕ} (hx : x < S.W) : 2 ^ x < 2 ^ S.W := Nat.pow_lt_pow_right (by norm_num) hx

theorem small_L_pow {i : ℕ} (hi : i ≤ S.Q) : S.L ^ i < 2 ^ S.W :=
  S.small (by have := S.L_pow_le hi; have := S.K_le_T; omega)

theorem Nq_pow_lt {i : ℕ} (hi : i ≤ S.Q) : S.Nq ^ i < 2 ^ S.W := by
  have h1 : S.Nq ≤ 2 ^ S.Nq := Nat.lt_two_pow_self.le
  calc S.Nq ^ i ≤ (2 ^ S.Nq) ^ i := Nat.pow_le_pow_left h1 _
    _ = 2 ^ (S.Nq * i) := (pow_mul _ _ _).symm
    _ < 2 ^ S.W := Nat.pow_lt_pow_right (by norm_num) (by
        have h := S.QT_lt_W
        have h2 : S.Nq ≤ S.T + 2 := by simp only [T, Nq]; omega
        calc S.Nq * i ≤ (S.T + 2) * S.Q := Nat.mul_le_mul h2 hi
          _ = S.Q * (S.T + 2) := by ring
          _ ≤ (S.Q + 3) * (S.T + 2) := Nat.mul_le_mul (by omega) le_rfl
          _ < S.W := h)

theorem Sizes : Lag.Sizes S.W S.M S.B := by
  have hfac : (S.M + 1).factorial < 2 ^ S.B := by
    calc (S.M + 1).factorial ≤ (S.M + 1) ^ (S.M + 1) := Nat.factorial_le_pow _
      _ ≤ (2 ^ (S.M + 1)) ^ (S.M + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2 ^ ((S.M + 1) * (S.M + 1)) := (pow_mul _ _ _).symm
      _ < 2 ^ S.B := Nat.pow_lt_pow_right (by norm_num) (by simp only [B]; nlinarith)
  refine ⟨hfac, by simp only [B]; nlinarith, ?_, by simp only [B]; nlinarith⟩
  have h := S.T3_lt_W
  have h1 : S.M + 2 ≤ S.T + 2 := by have := S.M_le_T; omega
  calc S.B * (S.M + 2) = (S.M + 2) ^ 3 := by simp only [B]; ring
    _ ≤ (S.T + 2) ^ 3 := Nat.pow_le_pow_left h1 _
    _ < S.W := h

end Setup

/-- Variable indices of the global values. -/
structure Ctx where
  M : ℕ
  v : ℕ
  h : ℕ
  fw : ℕ
  tailT : ℕ
  headT : ℕ
  partT : ℕ
  layT : ℕ
  Q : ℕ
  L : ℕ
  K : ℕ
  B : ℕ
  Nq : ℕ
  r : ℕ
  J : ℕ
  two : ℕ
  Eb : ℕ
  Bx : ℕ
  Pw : ℕ
  depth : ℕ
  lt : Lits

/-- One more binder. -/
def Ctx.up (c : Ctx) : Ctx where
  M := c.M + 1
  v := c.v + 1
  h := c.h + 1
  fw := c.fw + 1
  tailT := c.tailT + 1
  headT := c.headT + 1
  partT := c.partT + 1
  layT := c.layT + 1
  Q := c.Q + 1
  L := c.L + 1
  K := c.K + 1
  B := c.B + 1
  Nq := c.Nq + 1
  r := c.r + 1
  J := c.J + 1
  two := c.two + 1
  Eb := c.Eb + 1
  Bx := c.Bx + 1
  Pw := c.Pw + 1
  depth := c.depth + 1
  lt := c.lt

/-- The environment holds the global values at the indices of `c`. -/
structure Agree (S : Setup) (c : Ctx) (env : List ℕ) : Prop where
  M : env.getD c.M 0 = S.M
  v : env.getD c.v 0 = S.v
  h : env.getD c.h 0 = S.h
  fw : env.getD c.fw 0 = S.fw
  tailT : env.getD c.tailT 0 = S.tailT
  headT : env.getD c.headT 0 = S.headT
  partT : env.getD c.partT 0 = S.partT
  layT : env.getD c.layT 0 = S.layT
  Q : env.getD c.Q 0 = S.Q
  L : env.getD c.L 0 = S.L
  K : env.getD c.K 0 = S.K
  B : env.getD c.B 0 = S.B
  Nq : env.getD c.Nq 0 = S.Nq
  r : env.getD c.r 0 = S.r
  J : env.getD c.J 0 = S.J
  two : env.getD c.two 0 = S.two
  Eb : env.getD c.Eb 0 = S.Eb
  Bx : env.getD c.Bx 0 = S.Bx
  Pw : env.getD c.Pw 0 = S.Pw
  core : ∃ pre : List ℕ, pre.length = c.depth ∧ env = pre ++ S.core
  lt : c.lt = S.lt

theorem Agree.up {S : Setup} {c : Ctx} {env : List ℕ} (h : Agree S c env) (x : ℕ) :
    Agree S c.up (x :: env) where
  M := h.M
  v := h.v
  h := h.h
  fw := h.fw
  tailT := h.tailT
  headT := h.headT
  partT := h.partT
  layT := h.layT
  Q := h.Q
  L := h.L
  K := h.K
  B := h.B
  Nq := h.Nq
  r := h.r
  J := h.J
  two := h.two
  Eb := h.Eb
  Bx := h.Bx
  Pw := h.Pw
  core := by
    obtain ⟨pre, h1, h2⟩ := h.core
    exact ⟨x :: pre, by simp [h1, Ctx.up], by simp [h2]⟩
  lt := h.lt

end OnePigeonhole.Pseudo.Leaf
