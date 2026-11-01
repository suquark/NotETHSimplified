import TransposeBase.Limits

/-!
# The crossing of two wires -/

set_option linter.unusedSectionVars false

namespace TransposeBase
namespace Sector

open scoped BigOperators
open Finset Matrix

variable {k : Type*} [Field k] [CharZero k]

/-- A bit in `k`. -/
def bt (b : Bool) : k := if b then 1 else 0

/-- The equality tensor. -/
def dl (x y : Bool) : k := if x = y then 1 else 0

/-- The antisymmetric tensor. -/
def ep (x y : Bool) : k := bt y - bt x

/-- **The recoupling identity.** -/
theorem skein (a b c e : Bool) :
    (dl a c * dl b e : k) = dl a e * dl b c + ep a b * ep c e := by
  cases a <;> cases b <;> cases c <;> cases e <;> simp [dl, ep, bt]

/-! ### Tensor products -/

variable {p : ℕ}

/-! ### Disjoint pairs and many cuts -/

variable {Q' : ℕ}

end Sector
end TransposeBase
