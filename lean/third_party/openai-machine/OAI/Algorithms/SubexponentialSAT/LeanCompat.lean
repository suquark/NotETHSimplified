/- Local compatibility adaptation for Lean 4.33.1, 2026-10-29.
   See patches/lean-4.33.1.patch; theorem statements and definitions are preserved. -/
/- Modified locally on 2026-10-29: restrict imports for the isolated
Lean 4.33.1 package; compatibility declarations below are unchanged. -/
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

universe u v

-- Compatibility with the newer simplifier names used upstream.
alias ite_eq_left := if_pos
alias ite_eq_right := if_neg
alias dite_eq_left := dif_pos
alias dite_eq_right := dif_neg

/-!
Compatibility names for the Lean and Mathlib version used by this repository.
These are direct aliases of renamed library lemmas; they do not change any
definitions or proof obligations in the imported development.
-/

namespace List

theorem map_coe_finRange (n : ℕ) : (finRange n).map Fin.val = range n := by
  rw [← ofFn_eq_map]
  simp [ofFn_eq_pmap]

theorem finRange_map_get {α : Type u} (l : List α) : (finRange l.length).map l.get = l :=
  map_get_finRange l

end List

namespace Function

theorem update_same {α : Sort u} {β : α → Sort v} [DecidableEq α]
    (a : α) (value : β a) (f : (a : α) → β a) :
    update f a value a = value :=
  update_self a value f

theorem update_noteq {α : Sort u} {β : α → Sort v} [DecidableEq α]
    {a a' : α} (h : a ≠ a') (value : β a') (f : (a : α) → β a) :
    update f a' value a = f a :=
  update_of_ne h value f

end Function

namespace Nat

theorem le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} :
    x ≤ b ^ y ↔ clog b x ≤ y :=
  (clog_le_iff_le_pow hb).symm

theorem pow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x y : ℕ} :
    b ^ y < x ↔ y < clog b x :=
  (lt_clog_iff_pow_lt hb).symm

end Nat
