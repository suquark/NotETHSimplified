import SatBase.RulePriority

/-! The binary-degree invariant follows from rule priority and set
inclusions. Normalization can only decrease a literal's degree. -/
namespace SatBase

variable {n : ℕ}

theorem binaryDegree_mono {F G : ClauseSet (SignedLiteral n)} (h : F⊆G)
    (a : SignedLiteral n) : (coreClauses F 2 {a}).card≤(coreClauses G 2 {a}).card := by
  apply Finset.card_le_card
  intro C hC
  obtain ⟨hCF,hrest⟩ := Finset.mem_filter.mp hC
  exact Finset.mem_filter.mpr ⟨h hCF,hrest⟩

theorem binaryDegree_union_le (F G : ClauseSet (SignedLiteral n)) (a : SignedLiteral n) :
    (coreClauses (F∪G) 2 {a}).card≤(coreClauses F 2 {a}).card+(coreClauses G 2 {a}).card := by
  have he : coreClauses (F∪G) 2 {a}=coreClauses F 2 {a}∪coreClauses G 2 {a} :=
    Finset.filter_union _ _ _
  rw [he]
  exact Finset.card_union_le _ _

theorem binaryDegree_singleton_le (S : Finset (SignedLiteral n)) (a : SignedLiteral n) :
    (coreClauses {S} 2 {a}).card≤1 := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem binaryDegree_normalize_le (F : ClauseSet (SignedLiteral n)) (a : SignedLiteral n) :
    (coreClauses (normalizeClauses F) 2 {a}).card≤(coreClauses F 2 {a}).card :=
  binaryDegree_mono (normalizeClauses_subset F) a

theorem petals_core_degree_zero (F : ClauseSet (SignedLiteral n)) (w : ℕ)
    (S : Finset (SignedLiteral n)) (a : SignedLiteral n) (ha : a∈S) :
    (coreClauses (corePetals F w S) 2 {a}).card=0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro P hP hrest
  obtain ⟨C,_,rfl⟩ := Finset.mem_image.mp hP
  have hp : a∈C\S := hrest.2 (Finset.mem_singleton_self a)
  exact (Finset.mem_sdiff.mp hp).2 ha

/-- Binary petals containing b come from ternary clauses containing a and b. -/
theorem singleton_petals_degree_le (F : ClauseSet (SignedLiteral n)) (a b : SignedLiteral n) :
    (coreClauses (corePetals F 3 {a}) 2 {b}).card≤(coreClauses F 3 {a,b}).card := by
  have hs : coreClauses (corePetals F 3 {a}) 2 {b}⊆
      (coreClauses F 3 {a,b}).image (fun C => C\{a}) := by
    intro P hP
    obtain ⟨hP,hwidth,hb⟩ := Finset.mem_filter.mp hP
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hCF,hwidthC,ha⟩ := Finset.mem_filter.mp hC
    have hbc : b∈C := (Finset.mem_sdiff.mp (hb (Finset.mem_singleton_self b))).1
    apply Finset.mem_image.mpr
    refine ⟨C,Finset.mem_filter.mpr ⟨hCF,hwidthC,?_⟩,rfl⟩
    simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using
      And.intro (ha (Finset.mem_singleton_self a)) hbc
  exact (Finset.card_le_card hs).trans Finset.card_image_le

theorem left_degree_le (F : ClauseSet (SignedLiteral n)) (w : ℕ)
    (S : Finset (SignedLiteral n)) (a : SignedLiteral n) :
    (coreClauses (normalizedCoreLeft F w S) 2 {a}).card≤
      (coreClauses F 2 {a}).card+(coreClauses {S} 2 {a}).card := by
  apply (binaryDegree_normalize_le (insert S F) a).trans
  simpa only [Finset.union_singleton] using binaryDegree_union_le F {S} a

theorem right_degree_le (F : ClauseSet (SignedLiteral n)) (w : ℕ)
    (S : Finset (SignedLiteral n)) (a : SignedLiteral n) :
    (coreClauses (normalizedCoreRight F w S) 2 {a}).card≤
      (coreClauses F 2 {a}).card+(coreClauses (corePetals F w S) 2 {a}).card :=
  (binaryDegree_normalize_le _ a).trans (binaryDegree_union_le F (corePetals F w S) a)

/-- A ternary rule is selected only after all binary degrees are below L.
Adding its single core clause increases each binary degree by at most one. -/
theorem ternary_left_binaryDegree (F : ClauseSet (SignedLiteral n))
    (L : ℕ) (S : Finset (SignedLiteral n))
    (hr : chooseSparseRule F L=some (3,S)) (a : SignedLiteral n) :
    (coreClauses (normalizedCoreLeft F 3 S) 2 {a}).card<2*L := by
  have hd := ternary_rule_binary_bound F L S hr a
  have hl := left_degree_le F 3 S a
  have hn := binaryDegree_singleton_le S a
  omega

/-- Binary petals arise only from a singleton ternary core. Rule priority
bounds their degree by L, as well as the old binary degree. -/
theorem singleton_ternary_right_binaryDegree (F : ClauseSet (SignedLiteral n))
    (L : ℕ) (b : SignedLiteral n)
    (hr : chooseSparseRule F L=some (3,{b})) (a : SignedLiteral n) :
    (coreClauses (normalizedCoreRight F 3 {b}) 2 {a}).card<2*L := by
  have hd := ternary_rule_binary_bound F L {b} hr a
  have hright := right_degree_le F 3 {b} a
  by_cases hab : b=a
  · subst a
    have hp := petals_core_degree_zero F 3 {b} b (Finset.mem_singleton_self b)
    omega
  · have hp := singleton_petals_degree_le F b a
    have hb := singleton_ternary_pair_bound F L b b a hr hab
    omega

end SatBase
