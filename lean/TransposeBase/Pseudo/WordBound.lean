import TransposeBase.Pseudo.Lang

/-!
# All values are words

If the environment holds words below `2 ^ W`, then every value of every expression is below `2 ^ W`. So the
language has one data type, and a word operation is an operation on `W` bits.
-/

namespace TransposeBase.Pseudo

variable (W : ℕ)

private theorem foldl_lt {P : ℕ → Prop} (f : ℕ → ℕ → ℕ) (l : List ℕ) (s : ℕ) (hs : P s)
    (hf : ∀ st k, P st → k ∈ l → P (f st k)) : P (l.foldl f s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons k l ih =>
    exact ih (f s k) (hf s k hs (by simp)) fun st k' h1 h2 => hf st k' h1 (List.mem_cons_of_mem _ h2)

private theorem word_getD {env : List ℕ} (h : ∀ x ∈ env, x < 2 ^ W) (i : ℕ) : env.getD i 0 < 2 ^ W := by
  by_cases hi : i < env.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    positivity

/-- **Every value is a word.** -/
theorem eval_lt_word (e : Expr) (env : List ℕ) (h : ∀ x ∈ env, x < 2 ^ W) : eval W e env < 2 ^ W := by
  have hpos : 0 < 2 ^ W := by positivity
  induction e generalizing env with
  | var i => exact word_getD W h i
  | lit n => exact Nat.mod_lt _ hpos
  | add a b _ _ => exact Nat.mod_lt _ hpos
  | sub a b _ _ => exact Nat.mod_lt _ hpos
  | mul a b _ _ => exact Nat.mod_lt _ hpos
  | div a b iha _ => exact lt_of_le_of_lt (Nat.div_le_self _ _) (iha env h)
  | mod a b iha _ => exact lt_of_le_of_lt (Nat.mod_le _ _) (iha env h)
  | pow2 a _ =>
    simp only [eval]
    split_ifs with hlt
    · exact Nat.pow_lt_pow_right (by norm_num) hlt
    · exact hpos
  | ite a b c d _ _ ihc ihd =>
    simp only [eval]
    split_ifs
    · exact ihc env h
    · exact ihd env h
  | letE a b iha ihb =>
    refine ihb _ fun x hx => ?_
    rcases List.mem_cons.mp hx with rfl | hx
    · exact iha env h
    · exact h x hx
  | fold n s b ihn ihs ihb =>
    simp only [eval]
    have hnv := ihn env h
    refine foldl_lt (P := fun x => x < 2 ^ W) _ _ _ (ihs env h) fun st k hst hk => ihb _ fun x hx => ?_
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hst
    · exact lt_trans (List.mem_range.mp hk) hnv
    · exact h x hx
  | sum n b _ _ =>
    simp only [eval]
    exact foldl_lt (P := fun x => x < 2 ^ W) _ _ _ hpos fun _ _ _ _ => Nat.mod_lt _ hpos
  | prod n b _ _ =>
    simp only [eval]
    exact foldl_lt (P := fun x => x < 2 ^ W) _ _ _ (Nat.mod_lt _ hpos) fun _ _ _ _ => Nat.mod_lt _ hpos
  | sumIter n s f b ihn ihs ihf _ =>
    simp only [eval]
    have key : ∀ m,
        ((List.range m).foldl (fun p _ => (eval W f (p.1 :: env), (p.2 + eval W b (p.1 :: env)) % 2 ^ W))
          (eval W s env, 0)).1 < 2 ^ W ∧
        ((List.range m).foldl (fun p _ => (eval W f (p.1 :: env), (p.2 + eval W b (p.1 :: env)) % 2 ^ W))
          (eval W s env, 0)).2 < 2 ^ W := by
      intro m
      induction m with
      | zero => exact ⟨ihs env h, hpos⟩
      | succ m ih =>
        rw [List.range_succ, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        refine ⟨ihf _ fun x hx => ?_, Nat.mod_lt _ hpos⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ih.1
        · exact h x hx
    exact (key _).2

end TransposeBase.Pseudo
