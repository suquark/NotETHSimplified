import TransposeBase.Pseudo.PlaceCore

/-!
# The placement as a program -/

set_option linter.unusedSectionVars false

namespace TransposeBase.Pseudo.Place

open Finset TransposeBase.General TransposeBase.Spread TransposeBase.Pseudo.Code

/-! ### The cells of the wires -/

/-- The part of an end of the wire `f`: `P` is the table of parts, `T` the table of tails or of heads. -/
def ptN (fw P T f : ℕ) : ℕ := fld fw P (fld fw T f)

/-- The part of an end of the wire in the variable `ix`. -/
def endPartE (iT iP ix ifw : ℕ) : Expr := .letE (fieldE iT ix ifw) (fieldE (iP + 1) 0 (ifw + 1))

theorem ops_endPartE (W iT iP ix ifw : ℕ) (env : List ℕ) : ops W (endPartE iT iP ix ifw) env = 19 := by
  simp [endPartE, ops, ops_fieldE]

theorem eval_endPartE {W m v fw K : ℕ} (B : Bd W m v fw K) {iT iP ix ifw T P x : ℕ} {env : List ℕ}
    (ht : env.getD iT 0 = T) (hp : env.getD iP 0 = P) (hx : env.getD ix 0 = x)
    (hf : env.getD ifw 0 = fw) (hxm : x < m) (hT : fld fw T x < v) :
    eval W (endPartE iT iP ix ifw) env = ptN fw P T x := by
  have h1 : eval W (fieldE iT ix ifw) env = fld fw T x :=
    eval_fieldE ht hx hf (B.idx_lt (by omega)) B.fw_lt
  rw [endPartE, eval_letE, h1]
  exact eval_fieldE (by simpa using hp) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt

end TransposeBase.Pseudo.Place
