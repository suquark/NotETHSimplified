import TransposeBase.General
import TransposeBase.Pseudo.Words
import TransposeBase.Pseudo.Code

/-!
# The placement as a program: the map from nodes to parts -/

set_option linter.unusedSectionVars false

namespace TransposeBase.Pseudo.Place

open Finset TransposeBase.General TransposeBase.Spread

theorem eval_letE (W : ℕ) (a b : Expr) (env : List ℕ) :
    eval W (.letE a b) env = eval W b (eval W a env :: env) := rfl

/-! ### Fields -/

/-- Field `i` of the table `t`, for the field width `fw`. -/
def fld (fw t i : ℕ) : ℕ := t / 2 ^ (i * fw) % 2 ^ fw

theorem fld_add_low (fw s w : ℕ) {u α : ℕ} (hu : u < α) :
    fld fw (s + w * 2 ^ (α * fw)) u = fld fw s u := by
  unfold fld
  have h : 2 ^ (α * fw) = 2 ^ (u * fw) * 2 ^ fw * 2 ^ ((α - u - 1) * fw) := by
    rw [← pow_add, ← pow_add]
    congr 1
    obtain ⟨d, rfl⟩ : ∃ d, α = u + 1 + d := ⟨α - u - 1, by omega⟩
    have : u + 1 + d - u - 1 = d := by omega
    rw [this]
    ring
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self s]
  congr 1
  have h2 : w * (2 ^ (u * fw) * 2 ^ fw * 2 ^ ((α - u - 1) * fw)) =
      2 ^ (u * fw) * 2 ^ fw * (w * 2 ^ ((α - u - 1) * fw)) := by ring
  rw [h, h2, Nat.add_mul_mod_self_left]

theorem fld_add_self {fw s w α : ℕ} (hs : s < 2 ^ (α * fw)) (hw : w < 2 ^ fw) :
    fld fw (s + w * 2 ^ (α * fw)) α = w := by
  unfold fld
  rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hs, zero_add, Nat.mod_eq_of_lt hw]

theorem add_mul_lt {fw s w α : ℕ} (hs : s < 2 ^ (α * fw)) (hw : w < 2 ^ fw) :
    s + w * 2 ^ (α * fw) < 2 ^ ((α + 1) * fw) := by
  have : 2 ^ ((α + 1) * fw) = 2 ^ fw * 2 ^ (α * fw) := by rw [← pow_add]; congr 1; ring
  rw [this]
  have h1 : (w + 1) * 2 ^ (α * fw) ≤ 2 ^ fw * 2 ^ (α * fw) := Nat.mul_le_mul_right _ hw
  nlinarith

/-- A table with the fields `f e`, for `e < M`. -/
def pk (fw : ℕ) (f : ℕ → ℕ) (M : ℕ) : ℕ := ∑ e ∈ range M, f e * 2 ^ (e * fw)

theorem pk_succ (fw : ℕ) (f : ℕ → ℕ) (M : ℕ) : pk fw f (M + 1) = pk fw f M + f M * 2 ^ (M * fw) := by
  simp [pk, sum_range_succ]

theorem pk_lt {fw M : ℕ} {f : ℕ → ℕ} (hf : ∀ e < M, f e < 2 ^ fw) : pk fw f M < 2 ^ (M * fw) := by
  induction M with
  | zero => simp [pk]
  | succ M ih =>
    rw [pk_succ]
    exact add_mul_lt (ih fun e he => hf e (by omega)) (hf M (by omega))

theorem fld_pk {fw M : ℕ} {f : ℕ → ℕ} (hf : ∀ e < M, f e < 2 ^ fw) {i : ℕ} (hi : i < M) :
    fld fw (pk fw f M) i = f i := by
  induction M with
  | zero => omega
  | succ M ih =>
    have hlt := pk_lt (fw := fw) (M := M) (f := f) fun e he => hf e (by omega)
    rw [pk_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · rw [fld_add_low _ _ _ h]
      exact ih (fun e he => hf e (by omega)) h
    · exact fld_add_self hlt (hf _ (by omega))

/-- Reading field `i` of `t`, for variables `t`, `i`, `fw`. -/
def fieldE (t i fw : ℕ) : Expr :=
  .mod (.div (.var t) (.pow2 (.mul (.var i) (.var fw)))) (.pow2 (.var fw))

theorem eval_fieldE {W t i fw tv iv f : ℕ} {env : List ℕ} (ht : env.getD t 0 = tv)
    (hi : env.getD i 0 = iv) (hf : env.getD fw 0 = f) (h1 : iv * f < W) (h2 : f < W) :
    eval W (fieldE t i fw) env = fld f tv iv := by
  have h3 : iv * f < 2 ^ W := h1.trans Nat.lt_two_pow_self
  simp only [fieldE, eval, ht, hi, hf, Nat.mod_eq_of_lt h3, if_pos h1, if_pos h2, fld]

theorem ops_fieldE (W t i fw : ℕ) (env : List ℕ) : ops W (fieldE t i fw) env = 9 := by
  simp [fieldE, ops]

/-! ### The sizes -/

/-- What the programs need from the field width and the word size. -/
structure Bd (W m v fw K : ℕ) : Prop where
  hfw : K + v + 4 * m < 2 ^ fw
  hW : (m + v + 8) * fw ≤ W
  hK : 0 < K

namespace Bd

variable {W m v fw K : ℕ}

theorem fw_pos (B : Bd W m v fw K) : 0 < fw := by
  rcases Nat.eq_zero_or_pos fw with h | h
  · have := B.hfw
    have := B.hK
    simp [h] at *
    omega
  · exact h

theorem idx_lt (B : Bd W m v fw K) {i : ℕ} (hi : i ≤ m + v + 7) : i * fw < W := by
  have hp := B.fw_pos
  calc i * fw < (i + 1) * fw := by nlinarith
    _ ≤ (m + v + 8) * fw := Nat.mul_le_mul_right _ (by omega)
    _ ≤ W := B.hW

theorem fw_lt (B : Bd W m v fw K) : fw < W := by
  simpa using B.idx_lt (i := 1) (by omega)

theorem pow4 (B : Bd W m v fw K) : (2 ^ fw) ^ 4 ≤ 2 ^ W := by
  rw [← pow_mul]
  refine Nat.pow_le_pow_right (by norm_num) (le_trans ?_ B.hW)
  nlinarith

theorem two_le_pow (B : Bd W m v fw K) : 2 ≤ 2 ^ fw := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ fw := Nat.pow_le_pow_right (by norm_num) B.fw_pos

theorem pow_lt (B : Bd W m v fw K) : 2 ^ fw < 2 ^ W :=
  Nat.pow_lt_pow_right (by norm_num) B.fw_lt

theorem K_lt (B : Bd W m v fw K) : K < 2 ^ fw := by have := B.hfw; omega
theorem m_lt (B : Bd W m v fw K) : m < 2 ^ fw := by have := B.hfw; omega
theorem v_lt (B : Bd W m v fw K) : v < 2 ^ fw := by have := B.hfw; omega

theorem mul_lt (B : Bd W m v fw K) {a b : ℕ} (ha : a < 2 ^ fw) (hb : b < 2 ^ fw) : a * b < 2 ^ W := by
  have h2 := B.two_le_pow
  calc a * b < 2 ^ fw * 2 ^ fw := Nat.mul_lt_mul'' ha hb
    _ ≤ (2 ^ fw) ^ 4 := by
      have : (2 ^ fw) ^ 4 = 2 ^ fw * 2 ^ fw * (2 ^ fw * 2 ^ fw) := by ring
      rw [this]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ _ := B.pow4

theorem lit_K (B : Bd W m v fw K) : K < 2 ^ W := B.K_lt.trans B.pow_lt

theorem one_lt (B : Bd W m v fw K) : 1 < 2 ^ W := by
  have := B.two_le_pow
  have := B.pow_lt
  omega

end Bd

/-! ### The estimator on a word -/

/-- A network given by tables. -/
structure NetT {m v : ℕ} (fw tT hT : ℕ) (tail head : Fin m → Fin v) : Prop where
  tail_eq : ∀ e : Fin m, fld fw tT e = tail e
  head_eq : ∀ e : Fin m, fld fw hT e = head e

/-! ### The map from nodes to parts -/

/-- Setting the field `a` of the word `s` to `w`, for variables. -/
def setE (s w a f : ℕ) : Expr := .add (.var s) (.mul (.var w) (.pow2 (.mul (.var a) (.var f))))

theorem eval_setE {W s w a f : ℕ} {env : List ℕ} (ha : env.getD a 0 * env.getD f 0 < W)
    (h : env.getD s 0 + env.getD w 0 * 2 ^ (env.getD a 0 * env.getD f 0) < 2 ^ W) :
    eval W (setE s w a f) env =
      env.getD s 0 + env.getD w 0 * 2 ^ (env.getD a 0 * env.getD f 0) := by
  have h3 : env.getD a 0 * env.getD f 0 < 2 ^ W := ha.trans Nat.lt_two_pow_self
  have h4 : env.getD w 0 * 2 ^ (env.getD a 0 * env.getD f 0) < 2 ^ W := by omega
  simp only [setE, eval, Nat.mod_eq_of_lt h3, if_pos ha, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h]

theorem ops_setE (W s w a f : ℕ) (env : List ℕ) : ops W (setE s w a f) env = 8 := by
  simp [setE, ops]

end TransposeBase.Pseudo.Place
