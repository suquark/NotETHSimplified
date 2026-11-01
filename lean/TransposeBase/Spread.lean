import Mathlib

/-!
# Spreading the wires -/

set_option linter.unusedSectionVars false

namespace TransposeBase
namespace Spread

open scoped BigOperators
open Finset

variable {E V W : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V] [Fintype W]
  [DecidableEq W]

/-- The number of wires at a node. -/
def arity (tail head : E → V) (a : V) : ℕ :=
  (univ.filter fun e => tail e = a ∨ head e = a).card

end Spread
end TransposeBase
