import TransposeBase.Arith
import TransposeBase.Spread

/-!
# Gluing and factorization for general tensor networks -/

set_option linter.unusedSectionVars false

namespace TransposeBase
namespace General

open scoped BigOperators
open Finset

/-! ## Merging blocks -/

/-! ## Gluing and factorization for wires -/

section Wires

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
variable {Q : ℕ} {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  {k : Type*} [CommRing k]

/-- The wires at the node `α`. -/
abbrev Inc (tail head : E → V) (α : V) := {e : E // tail e = α ∨ head e = α}

/-- The input of the node `α`: the `X` copy on wires with tail `α`, and the `Y` copy on the others. -/
def read (tail head : E → V) (α : V) (x y : E → Bool) : Inc tail head α → Bool :=
  fun e => if tail e.1 = α then x e.1 else y e.1


/-- The node that reads a used bit: `Sum.inl e` is the `X` copy, `Sum.inr e` the `Y` copy. -/
def bitVertex (tail head : E → V) : E ⊕ E → V := Sum.elim tail head

/-- The merged block of `P_t` that contains a used bit. -/
def bitBlock (r : V → Word Q C) (tail head : E → V) (t : Fin Q) (i : E ⊕ E) : C :=
  r (bitVertex tail head i) t

/-- The used bits in the merged block `g` of `P_t`. -/
abbrev BlockBits (r : V → Word Q C) (tail head : E → V) (t : Fin Q) (g : C) :=
  {i : E ⊕ E // bitBlock r tail head t i = g}

/-- An assignment of the used bits of block `g`, extended by `false`. -/
def blockExt (r : V → Word Q C) (tail head : E → V) (t : Fin Q) (g : C)
    (v : BlockBits r tail head t g → Bool) : E ⊕ E → Bool :=
  fun i => if h : bitBlock r tail head t i = g then v ⟨i, h⟩ else false

/-! ## The size of a merged block -/

end Wires

/-! ## The finer alphabet -/

/-! ## The numbers of the placement -/

end General
end TransposeBase
