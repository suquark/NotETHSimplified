import SatBase.SparsificationRules
import SatBase.ClauseInsertion

/-! The clauses inserted by a core split are new, have uniform smaller
width, and cannot be removed by an old subclause during normalization. -/
namespace SatBase

variable {A : Type*} [DecidableEq A]

theorem core_no_old_subclause (F : ClauseSet A)
    (hanti : ∀ C∈F,∀ D∈F,C⊆D → C=D) (w : ℕ) (S : Finset A)
    (hS : S.card<w) (ha : (coreClauses F w S).Nonempty) :
    ∀ D∈F,¬D⊆S := by
  obtain ⟨C,hC⟩ := ha
  have hc := Finset.mem_filter.mp hC
  intro D hD hDS
  have he := hanti D hD C hc.1 (hDS.trans hc.2.2)
  have hcard := Finset.card_le_card hDS
  rw [he,hc.2.1] at hcard
  omega

theorem petal_no_old_subclause (F : ClauseSet A)
    (hanti : ∀ C∈F,∀ D∈F,C⊆D → C=D) (w : ℕ) (S : Finset A)
    (hS : S.Nonempty) : ∀ P∈corePetals F w S,∀ D∈F,¬D⊆P := by
  intro P hP D hD hDP
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hP
  have hc := Finset.mem_filter.mp hC
  have he := hanti D hD C hc.1 (hDP.trans Finset.sdiff_subset)
  obtain ⟨a,ha⟩ := hS
  have hCa := hc.2.2 ha
  have hnot := (Finset.mem_sdiff.mp (hDP (by simpa only [he] using hCa))).2
  exact hnot ha

theorem sparseCandidate_width {n : ℕ} (r : ℕ × Finset (SignedLiteral n))
    (h : r∈sparseCandidates n) : r.1=2 ∨ r.1=3 := by
  simp only [sparseCandidates,List.mem_append,List.mem_map,List.mem_flatMap] at h
  rcases h with ((h | h) | h)
  · obtain ⟨a,_,rfl⟩ := h
    exact Or.inl rfl
  · obtain ⟨a,_,b,_,rfl⟩ := h
    exact Or.inr rfl
  · obtain ⟨a,_,rfl⟩ := h
    exact Or.inr rfl

theorem coreLeft_width {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (hw : ∀ C∈F,C.card≤3) (w : ℕ) (S : Finset (SignedLiteral n))
    (hS : S.card<w) (hw3 : w≤3) :
    ∀ C∈normalizedCoreLeft F w S,C.card≤3 := by
  intro C hC
  have hc := normalizeClauses_subset (coreLeft F w S) hC
  rcases Finset.mem_insert.mp hc with he | hc
  · subst C
    omega
  · exact hw C hc

theorem coreRight_width {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (hw : ∀ C∈F,C.card≤3) (w : ℕ) (S : Finset (SignedLiteral n)) (hw3 : w≤3) :
    ∀ C∈normalizedCoreRight F w S,C.card≤3 := by
  intro C hC
  have hc := normalizeClauses_subset (coreRight F w S) hC
  rcases Finset.mem_union.mp hc with hc | hc
  · exact hw C hc
  · rw [corePetal_width F w S hc]
    omega

/-- These facts apply to the rule actually returned by the finite search. -/
theorem chosen_rule_children {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (hw : ∀ C∈F,C.card≤3) (L : ℕ) (hL : 1≤L)
    (r : ℕ × Finset (SignedLiteral n)) (hr : chooseSparseRule F L=some r) :
    (∀ C∈normalizedCoreLeft F r.1 r.2,C.card≤3) ∧
    (∀ C∈normalizedCoreRight F r.1 r.2,C.card≤3) ∧
    (coreClauses F r.1 r.2).Nonempty := by
  obtain ⟨hmem,hS,hwidth,hcount⟩ := chooseSparseRule_sound F L r hr
  have hw3 : r.1≤3 := by rcases sparseCandidate_width r hmem with h | h <;> omega
  refine ⟨coreLeft_width F hw _ _ hwidth hw3,coreRight_width F hw _ _ hw3,?_⟩
  apply Finset.card_pos.mp
  have hp : 1≤L^(r.1-r.2.card) := one_le_pow₀ hL
  omega

/-- Freshness is derived for an already normalized input, rather than
assumed as a property of the selected core or its petals. -/
theorem chosen_rule_fresh {n : ℕ} (G : ClauseSet (SignedLiteral n))
    (L : ℕ) (hL : 1≤L) (r : ℕ × Finset (SignedLiteral n))
    (hr : chooseSparseRule (normalizeClauses G) L=some r) :
    (∀ D∈normalizeClauses G,¬D⊆r.2) ∧
    (∀ P∈corePetals (normalizeClauses G) r.1 r.2,∀ D∈normalizeClauses G,¬D⊆P) := by
  obtain ⟨_,hS,hwidth,hcount⟩ := chooseSparseRule_sound (normalizeClauses G) L r hr
  have hanti : ∀ C∈normalizeClauses G,∀ D∈normalizeClauses G,C⊆D → C=D :=
    fun _ hC _ hD hCD => normalizeClauses_antichain G hC hD hCD
  have ha : (coreClauses (normalizeClauses G) r.1 r.2).Nonempty := by
    apply Finset.card_pos.mp
    have hp : 1≤L^(r.1-r.2.card) := one_le_pow₀ hL
    omega
  exact ⟨core_no_old_subclause _ hanti _ _ hwidth ha,
    petal_no_old_subclause _ hanti _ _ hS⟩

theorem core_not_tautological {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (ht : ∀ C∈F,¬tautological C) (w : ℕ) (S : Finset (SignedLiteral n))
    (ha : (coreClauses F w S).Nonempty) : ¬tautological S := by
  obtain ⟨C,hC⟩ := ha
  have hc := Finset.mem_filter.mp hC
  intro hS
  exact ht C hc.1 (tautological_mono hc.2.2 hS)

theorem corePetals_not_tautological {n : ℕ} (F : ClauseSet (SignedLiteral n))
    (ht : ∀ C∈F,¬tautological C) (w : ℕ) (S : Finset (SignedLiteral n)) :
    ∀ P∈corePetals F w S,¬tautological P := by
  intro P hP hT
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hP
  exact ht C (Finset.mem_filter.mp hC).1 (tautological_mono Finset.sdiff_subset hT)

end SatBase
