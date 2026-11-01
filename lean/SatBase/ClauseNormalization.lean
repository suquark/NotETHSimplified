import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Init.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Card

/-! Clauses are finite sets of literals. Removing duplicate literals,
tautological clauses and subsumed clauses preserves every assignment. -/
namespace SatBase

abbrev SignedLiteral (n : ℕ) := Fin n × Bool
abbrev ClauseSet (A : Type*) := Finset (Finset A)

def holdsClause {A : Type*} (p : A → Prop) (C : Finset A) : Prop :=
  ∃ a∈C,p a

def holdsFormula {A : Type*} (p : A → Prop) (F : ClauseSet A) : Prop :=
  ∀ C∈F,holdsClause p C

instance holdsClauseDecidable {A : Type*} (p : A → Prop) [DecidablePred p]
    (C : Finset A) : Decidable (holdsClause p C) := by
  unfold holdsClause
  infer_instance

instance holdsFormulaDecidable {A : Type*} (p : A → Prop) [DecidablePred p]
    (F : ClauseSet A) : Decidable (holdsFormula p F) := by
  unfold holdsFormula
  infer_instance

theorem holdsClause_mono {A : Type*} (p : A → Prop) {C D : Finset A}
    (h : C⊆D) : holdsClause p C → holdsClause p D := by
  rintro ⟨a,ha,hp⟩
  exact ⟨a,h ha,hp⟩

/-- Keep exactly the clauses with no strict subclause in the formula. -/
def minimalClauses {A : Type*} [DecidableEq A] (F : ClauseSet A) : ClauseSet A :=
  F.filter (fun C => ¬∃ D∈F,D⊂C)

theorem minimalClauses_subset {A : Type*} [DecidableEq A] (F : ClauseSet A) :
    minimalClauses F⊆F := Finset.filter_subset _ _

/-- Every removed clause contains one of the retained clauses. -/
theorem contains_minimalClause {A : Type*} [DecidableEq A] (F : ClauseSet A)
    (C : Finset A) (hC : C∈F) : ∃ D∈minimalClauses F,D⊆C := by
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases h : ∃ D∈F,D⊂C
    · obtain ⟨D,hD,hDC⟩ := h
      obtain ⟨E,hE,hED⟩ := ih D hDC hD
      exact ⟨E,hE,hED.trans hDC.le⟩
    · exact ⟨C,Finset.mem_filter.mpr ⟨hC,h⟩,Finset.Subset.refl _⟩

theorem minimalClauses_equivalent {A : Type*} [DecidableEq A]
    (p : A → Prop) (F : ClauseSet A) :
    holdsFormula p (minimalClauses F) ↔ holdsFormula p F := by
  constructor
  · intro h C hC
    obtain ⟨D,hD,hDC⟩ := contains_minimalClause F C hC
    exact holdsClause_mono p hDC (h D hD)
  · intro h C hC
    exact h C (minimalClauses_subset F hC)

theorem minimalClauses_antichain {A : Type*} [DecidableEq A]
    (F : ClauseSet A) {C D : Finset A}
    (hC : C∈minimalClauses F) (hD : D∈minimalClauses F) (hCD : C⊆D) : C=D := by
  have hmin := (Finset.mem_filter.mp hD).2
  by_contra hne
  exact hmin ⟨C,minimalClauses_subset F hC,Finset.ssubset_iff_subset_ne.mpr ⟨hCD,hne⟩⟩

/-- A signed literal is true exactly when its sign equals its variable value. -/
def literalHolds {n : ℕ} (x : Fin n → Bool) (l : SignedLiteral n) : Prop :=
  x l.1=l.2

instance literalHoldsDecidable {n : ℕ} (x : Fin n → Bool) : DecidablePred (literalHolds x) := by
  intro l
  unfold literalHolds
  infer_instance

def tautological {n : ℕ} (C : Finset (SignedLiteral n)) : Prop :=
  ∃ v : Fin n,(v,false)∈C ∧ (v,true)∈C

instance tautologicalDecidable {n : ℕ} (C : Finset (SignedLiteral n)) :
    Decidable (tautological C) := by unfold tautological; infer_instance

theorem tautological_holds {n : ℕ} (C : Finset (SignedLiteral n))
    (h : tautological C) (x : Fin n → Bool) : holdsClause (literalHolds x) C := by
  obtain ⟨v,hf,ht⟩ := h
  cases hx : x v
  · exact ⟨(v,false),hf,hx⟩
  · exact ⟨(v,true),ht,hx⟩

def normalizeClauses {n : ℕ} (F : ClauseSet (SignedLiteral n)) :
    ClauseSet (SignedLiteral n) :=
  minimalClauses (F.filter (fun C => ¬tautological C))

theorem normalizeClauses_subset {n : ℕ} (F : ClauseSet (SignedLiteral n)) :
    normalizeClauses F⊆F := (minimalClauses_subset _).trans (Finset.filter_subset _ _)

theorem normalizeClauses_equivalent {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (x : Fin n → Bool) :
    holdsFormula (literalHolds x) (normalizeClauses F) ↔ holdsFormula (literalHolds x) F := by
  rw [normalizeClauses,minimalClauses_equivalent]
  constructor
  · intro h C hC
    by_cases ht : tautological C
    · exact tautological_holds C ht x
    · exact h C (Finset.mem_filter.mpr ⟨hC,ht⟩)
  · intro h C hC
    exact h C (Finset.mem_filter.mp hC).1

theorem normalizeClauses_antichain {n : ℕ} (F : ClauseSet (SignedLiteral n))
    {C D : Finset (SignedLiteral n)} (hC : C∈normalizeClauses F)
    (hD : D∈normalizeClauses F) (hCD : C⊆D) : C=D :=
  minimalClauses_antichain _ hC hD hCD

theorem normalizeClauses_not_tautological {n : ℕ} (F : ClauseSet (SignedLiteral n))
    {C : Finset (SignedLiteral n)} (hC : C∈normalizeClauses F) : ¬tautological C :=
  (Finset.mem_filter.mp (minimalClauses_subset _ hC)).2

theorem normalizeClauses_idempotent {n : ℕ} (F : ClauseSet (SignedLiteral n)) :
    normalizeClauses (normalizeClauses F)=normalizeClauses F := by
  apply Finset.Subset.antisymm (normalizeClauses_subset _)
  intro C hC
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hC,normalizeClauses_not_tautological F hC⟩,?_⟩
  rintro ⟨D,hD,hDC⟩
  exact hDC.ne (normalizeClauses_antichain F (Finset.mem_filter.mp hD).1 hC hDC.le)

end SatBase
