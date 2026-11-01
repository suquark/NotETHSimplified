import SatBase.ClauseNormalization

/-! Adding a batch of new clauses and then normalizing. Existing clauses
are removed exactly when they contain a new clause. This avoids a separate
remainder formula in the branching construction. -/
namespace SatBase

variable {A : Type*} [DecidableEq A]

theorem minimalClauses_addition (F N : ClauseSet A)
    (hF : ∀ C∈F,∀ D∈F,C⊆D → C=D)
    (hN : ∀ C∈N,∀ D∈N,C⊆D → C=D)
    (hnew : ∀ C∈N,∀ D∈F,¬D⊆C) :
    minimalClauses (F∪N)=N∪F.filter (fun C => ∀ D∈N,¬D⊆C) := by
  apply Finset.ext
  intro C
  constructor
  · intro hC
    obtain ⟨hmem,hmin⟩ := Finset.mem_filter.mp hC
    rcases Finset.mem_union.mp hmem with hCF | hCN
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hCF,?_⟩
      intro D hD hDC
      have hne : D≠C := by
        intro he
        exact hnew D hD C hCF (by simpa only [he] using (Finset.Subset.refl C))
      exact hmin ⟨D,Finset.mem_union_right _ hD,Finset.ssubset_iff_subset_ne.mpr ⟨hDC,hne⟩⟩
    · exact Finset.mem_union_left _ hCN
  · intro hC
    apply Finset.mem_filter.mpr
    rcases Finset.mem_union.mp hC with hCN | hCF
    · refine ⟨Finset.mem_union_right _ hCN,?_⟩
      rintro ⟨D,hD,hDC⟩
      rcases Finset.mem_union.mp hD with hDF | hDN
      · exact hnew C hCN D hDF hDC.le
      · exact hDC.ne (hN D hDN C hCN hDC.le)
    · obtain ⟨hCF,hkeep⟩ := Finset.mem_filter.mp hCF
      refine ⟨Finset.mem_union_left _ hCF,?_⟩
      rintro ⟨D,hD,hDC⟩
      rcases Finset.mem_union.mp hD with hDF | hDN
      · exact hDC.ne (hF D hDF C hCF hDC.le)
      · exact hkeep D hDN hDC.le

theorem tautological_mono {n : ℕ} {C D : Finset (SignedLiteral n)}
    (hCD : C⊆D) (hC : tautological C) : tautological D := by
  obtain ⟨v,hf,ht⟩ := hC
  exact ⟨v,hCD hf,hCD ht⟩

theorem normalizeClauses_addition {n : ℕ} (F N : ClauseSet (SignedLiteral n))
    (hF : ∀ C∈F,∀ D∈F,C⊆D → C=D)
    (hN : ∀ C∈N,∀ D∈N,C⊆D → C=D)
    (hnew : ∀ C∈N,∀ D∈F,¬D⊆C)
    (htF : ∀ C∈F,¬tautological C) (htN : ∀ C∈N,¬tautological C) :
    normalizeClauses (F∪N)=N∪F.filter (fun C => ∀ D∈N,¬D⊆C) := by
  have ht : (F∪N).filter (fun C => ¬tautological C)=F∪N := by
    apply Finset.filter_true_of_mem
    intro C hC
    rcases Finset.mem_union.mp hC with h | h
    · exact htF C h
    · exact htN C h
  rw [normalizeClauses,ht]
  apply Finset.ext
  intro C
  have h := Finset.ext_iff.mp (minimalClauses_addition (A:=SignedLiteral n) F N hF hN hnew) C
  simpa only [minimalClauses,Finset.mem_union,Finset.mem_filter] using h

end SatBase
