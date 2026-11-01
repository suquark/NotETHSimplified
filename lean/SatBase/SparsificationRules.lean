import SatBase.CoreBranching

/-! The three rule types are searched in their prescribed priority order.
The absence of a rule implies the terminal occurrence bound. -/
namespace SatBase
open scoped BigOperators

def literalOrder (n : ℕ) : List (SignedLiteral n) :=
  (List.finRange n).flatMap (fun v => [(v,false),(v,true)])

theorem mem_literalOrder {n : ℕ} (a : SignedLiteral n) : a∈literalOrder n := by
  rcases a with ⟨v,b⟩
  apply List.mem_flatMap.mpr
  refine ⟨v,by simp,?_⟩
  cases b <;> simp

def sparseCandidates (n : ℕ) : List (ℕ × Finset (SignedLiteral n)) :=
  (literalOrder n).map (fun a => (2,{a})) ++
  (literalOrder n).flatMap (fun a =>
    ((literalOrder n).filter (fun b => a≠b)).map (fun b => (3,{a,b}))) ++
  (literalOrder n).map (fun a => (3,{a}))

theorem sparseCandidate_binary {n : ℕ} (a : SignedLiteral n) :
    (2,{a})∈sparseCandidates n := by
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  exact List.mem_map.mpr ⟨a,mem_literalOrder a,rfl⟩

theorem sparseCandidate_ternary {n : ℕ} (a : SignedLiteral n) :
    (3,{a})∈sparseCandidates n := by
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨a,mem_literalOrder a,rfl⟩

def sparseEligible {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (r : ℕ × Finset (SignedLiteral n)) : Prop :=
  r.2.Nonempty ∧ r.2.card<r.1 ∧ L^(r.1-r.2.card)≤(coreClauses F r.1 r.2).card

instance sparseEligibleDecidable {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (r : ℕ × Finset (SignedLiteral n)) : Decidable (sparseEligible F L r) := by
  unfold sparseEligible
  infer_instance

def chooseSparseRule {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ) :
    Option (ℕ × Finset (SignedLiteral n)) :=
  (sparseCandidates n).find? (fun r => decide (sparseEligible F L r))

theorem chooseSparseRule_sound {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (r : ℕ × Finset (SignedLiteral n)) (h : chooseSparseRule F L=some r) :
    r∈sparseCandidates n ∧ sparseEligible F L r := by
  constructor
  · exact List.mem_of_find?_eq_some h
  · simpa only [decide_eq_true_eq] using List.find?_some h

theorem noSparseRule_ineligible {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (h : chooseSparseRule F L=none) (r : ℕ × Finset (SignedLiteral n))
    (hr : r∈sparseCandidates n) : ¬sparseEligible F L r := by
  simpa only [decide_eq_true_eq] using (List.find?_eq_none.mp h) r hr

theorem noSparseRule_binary {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (h : chooseSparseRule F L=none) (a : SignedLiteral n) :
    (coreClauses F 2 {a}).card<L := by
  have hn := noSparseRule_ineligible F L h (2,{a}) (sparseCandidate_binary a)
  by_contra hc
  apply hn
  simpa [sparseEligible] using (Nat.le_of_not_gt hc)

theorem noSparseRule_ternary {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (h : chooseSparseRule F L=none) (a : SignedLiteral n) :
    (coreClauses F 3 {a}).card<L^2 := by
  have hn := noSparseRule_ineligible F L h (3,{a}) (sparseCandidate_ternary a)
  by_contra hc
  apply hn
  simpa [sparseEligible] using (Nat.le_of_not_gt hc)

def literalOccurrences {n : ℕ} (F : ClauseSet (SignedLiteral n)) (a : SignedLiteral n) : ℕ :=
  (F.filter (fun C => a∈C)).card

theorem unit_literal_bound {n : ℕ} (F : ClauseSet (SignedLiteral n)) (a : SignedLiteral n) :
    (coreClauses F 1 {a}).card≤1 := by
  have hs : coreClauses F 1 {a}⊆{{a}} := by
    intro C hC
    have hc := (Finset.mem_filter.mp hC).2
    apply Finset.mem_singleton.mpr
    symm
    exact Finset.eq_of_subset_of_card_le hc.2 (by simpa only [Finset.card_singleton] using hc.1.le)
  simpa only [Finset.card_singleton] using Finset.card_le_card hs

theorem literalOccurrences_split {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (hw : ∀ C∈F,C.card≤3) (a : SignedLiteral n) :
    literalOccurrences F a≤(coreClauses F 1 {a}).card+
      (coreClauses F 2 {a}).card+(coreClauses F 3 {a}).card := by
  have hs : F.filter (fun C => a∈C)⊆
      (coreClauses F 1 {a}∪coreClauses F 2 {a})∪coreClauses F 3 {a} := by
    intro C hC
    obtain ⟨hCF,ha⟩ := Finset.mem_filter.mp hC
    have hp : 0<C.card := Finset.card_pos.mpr ⟨a,ha⟩
    have hwidth := hw C hCF
    have hsingle : {a}⊆C := Finset.singleton_subset_iff.mpr ha
    have hcases : C.card=1 ∨ C.card=2 ∨ C.card=3 := by omega
    rcases hcases with h1 | h2 | h3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hCF,h1,hsingle⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hCF,h2,hsingle⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hCF,h3,hsingle⟩)
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))

theorem noSparseRule_literal_bound {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (L : ℕ) (hw : ∀ C∈F,C.card≤3) (h : chooseSparseRule F L=none)
    (a : SignedLiteral n) : literalOccurrences F a≤1+L+L^2 := by
  have hs := literalOccurrences_split F hw a
  have h1 := unit_literal_bound F a
  have h2 := noSparseRule_binary F L h a
  have h3 := noSparseRule_ternary F L h a
  omega

def variableOccurrences {n : ℕ} (F : ClauseSet (SignedLiteral n)) (v : Fin n) : ℕ :=
  literalOccurrences F (v,false)+literalOccurrences F (v,true)

/-- This is the occurrence bound passed to the checked leaf counter. -/
theorem noSparseRule_variable_bound {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (L : ℕ) (hL : 2≤L) (hw : ∀ C∈F,C.card≤3) (h : chooseSparseRule F L=none)
    (v : Fin n) : variableOccurrences F v≤4*L^2 := by
  have hf := noSparseRule_literal_bound F L hw h (v,false)
  have ht := noSparseRule_literal_bound F L hw h (v,true)
  have hm : 2*L≤L^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right L hL
  have hs : 4≤L^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hL hL
  unfold variableOccurrences
  omega

end SatBase
