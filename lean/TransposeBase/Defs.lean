import Mathlib

/-! Definitions:
words, cells, partial transposes, the indicator `T`, and block products over `P_t`. -/
namespace TransposeBase
open scoped BigOperators

variable {Q : ℕ} {A : Type*}

/-- A word: a row or column index. -/
abbrev Word (Q : ℕ) (A : Type*) := Fin Q → A

/-- A cell `(u,w)` of a matrix: row `u`, column `w`. -/
abbrev Cell (Q : ℕ) (A : Type*) := Word Q A × Word Q A

/-- `τ_E`: exchange the digits in `E` of the row and the column. -/
def swap (E : Finset (Fin Q)) (ω : Cell Q A) : Cell Q A :=
  (fun i => if i ∈ E then ω.2 i else ω.1 i, fun i => if i ∈ E then ω.1 i else ω.2 i)

/-- The transposed cell. -/
def tr (ω : Cell Q A) : Cell Q A := (ω.2, ω.1)

variable {k : Type*} [CommRing k]

/-- `X` and `X'` agree on the rows whose digit `t` is `g`. -/
def AgreeOn (t : Fin Q) (g : A) (X X' : Cell Q A → k) : Prop :=
  ∀ ω : Cell Q A, ω.1 t = g → X ω = X' ω

/-- `Φ` is a function of block `g` of `P_t`: it reads `X` and `Y` only in rows with digit `t`
equal to `g`. -/
def IsBlockFun {M : Type*} (t : Fin Q) (g : A) (Φ : (Cell Q A → k) → (Cell Q A → k) → M) : Prop :=
  ∀ X X' Y Y', AgreeOn t g X X' → AgreeOn t g Y Y' → Φ X Y = Φ X' Y'

/-- A product over the blocks of `P_t` of functions of one block, valued in a ring `M`. -/
def IsBlockProduct {M : Type*} [CommMonoid M] [Fintype A] (t : Fin Q)
    (p : (Cell Q A → k) → (Cell Q A → k) → M) : Prop :=
  ∃ Φ : A → (Cell Q A → k) → (Cell Q A → k) → M,
    (∀ g, IsBlockFun t g (Φ g)) ∧ ∀ X Y, p X Y = ∏ g, Φ g X Y

/-- `f` is a linear combination of at most `n` products over the blocks of `P_t`, each with
values in `k`. This is the unit in which Theorem 1 counts. -/
def IsBlockSum [Fintype A] (t : Fin Q) (n : ℕ) (f : (Cell Q A → k) → (Cell Q A → k) → k) : Prop :=
  ∃ (c : Fin n → k) (p : Fin n → (Cell Q A → k) → (Cell Q A → k) → k),
    (∀ i, IsBlockProduct t (p i)) ∧ ∀ X Y, f X Y = ∑ i, c i * p i X Y

/-- The value `0` or `1` of a bit in the ring `k`. -/
def bit (b : Bool) : k := if b then 1 else 0

/-- On bit matrices, `Tind` is the indicator of `Y = Xᵀ`. -/
def IsTransposeIndicator [Fintype A] (Tind : (Cell Q A → k) → (Cell Q A → k) → k) : Prop :=
  ∀ X Y : Cell Q A → Bool, Tind (fun ω => bit (X ω)) (fun ω => bit (Y ω)) =
    if ∀ ω, Y ω = X (tr ω) then 1 else 0

end TransposeBase
