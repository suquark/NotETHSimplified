import SatBase.CoreFreshness

/-! Consequences of the actual first-match rule order. In particular,
ternary steps occur only after all heavy binary literals are absent. -/
namespace SatBase

private theorem find_prefix_none {A : Type*} (pre rest : List A) (p : A → Bool)
    (r : A) (h : (pre++rest).find? p=some r) (hr : r∉pre) : pre.find? p=none := by
  cases hp : pre.find? p with
  | none => rfl
  | some a =>
    have he : a=r := Option.some.inj (by simpa [List.find?_append,hp] using h)
    subst a
    exact False.elim (hr (List.mem_of_find?_eq_some hp))

theorem ternary_rule_binary_bound {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (S : Finset (SignedLiteral n)) (hr : chooseSparseRule F L=some (3,S))
    (a : SignedLiteral n) : (coreClauses F 2 {a}).card<L := by
  let pre : List (ℕ × Finset (SignedLiteral n)) := (literalOrder n).map (fun a => (2,{a}))
  let rest : List (ℕ × Finset (SignedLiteral n)) := (literalOrder n).flatMap (fun a =>
    ((literalOrder n).filter (fun b => a≠b)).map (fun b => (3,{a,b}))) ++
    (literalOrder n).map (fun a => (3,{a}))
  have hp : pre.find? (fun r => decide (sparseEligible F L r))=none := by
    apply find_prefix_none pre rest _ (3,S)
    · simpa only [pre,rest,chooseSparseRule,sparseCandidates,List.append_assoc] using hr
    · rintro hmem
      obtain ⟨b,_,he⟩ := List.mem_map.mp hmem
      have hfst := congrArg Prod.fst he
      norm_num at hfst
  have hn := (List.find?_eq_none.mp hp) (2,{a}) (List.mem_map.mpr ⟨a,mem_literalOrder a,rfl⟩)
  have hnot : ¬sparseEligible F L (2,{a}) := by simpa only [decide_eq_true_eq] using hn
  by_contra hc
  apply hnot
  simpa [sparseEligible] using Nat.le_of_not_gt hc

theorem singleton_ternary_pair_bound {n : ℕ} (F : ClauseSet (SignedLiteral n)) (L : ℕ)
    (a b c : SignedLiteral n) (hr : chooseSparseRule F L=some (3,{a})) (hbc : b≠c) :
    (coreClauses F 3 {b,c}).card<L := by
  let pre : List (ℕ × Finset (SignedLiteral n)) := (literalOrder n).map (fun a => (2,{a})) ++
    (literalOrder n).flatMap (fun a =>
      ((literalOrder n).filter (fun b => a≠b)).map (fun b => (3,{a,b})))
  let rest : List (ℕ × Finset (SignedLiteral n)) := (literalOrder n).map (fun a => (3,{a}))
  have hp : pre.find? (fun r => decide (sparseEligible F L r))=none := by
    apply find_prefix_none pre rest _ (3,{a}) hr
    · rintro hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · obtain ⟨b,_,he⟩ := List.mem_map.mp hmem
        have hfst := congrArg Prod.fst he
        norm_num at hfst
      · obtain ⟨b,_,hinner⟩ := List.mem_flatMap.mp hmem
        obtain ⟨c,hc,he⟩ := List.mem_map.mp hinner
        have hne : b≠c := by simpa only [decide_eq_true_eq] using (List.mem_filter.mp hc).2
        have hcards := congrArg (fun r : ℕ × Finset (SignedLiteral n) => r.2.card) he
        simp [hne] at hcards
  have hmem : (3,{b,c})∈pre := by
    apply List.mem_append.mpr
    right
    apply List.mem_flatMap.mpr
    refine ⟨b,mem_literalOrder b,?_⟩
    exact List.mem_map.mpr ⟨c,List.mem_filter.mpr ⟨mem_literalOrder c,by simpa using hbc⟩,rfl⟩
  have hn := (List.find?_eq_none.mp hp) (3,{b,c}) hmem
  have hnot : ¬sparseEligible F L (3,{b,c}) := by simpa only [decide_eq_true_eq] using hn
  by_contra hc
  apply hnot
  simpa [sparseEligible,hbc] using Nat.le_of_not_gt hc

end SatBase
