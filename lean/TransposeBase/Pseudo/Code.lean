import TransposeBase.Pseudo.Enum

/-!
# Sums over finite types as sums over ranges of numbers

A program sums over numbers in a range. These lemmas turn a sum over an abstract finite type into a sum over
`Finset.range`, and they give the decoding from the number to the element.

* A word `Fin Q → Fin G` is the list of the base-`G` digits of a number below `G ^ Q`.
* An element `t : Fin n` is a number `k < n`.
* An element of a subtype `{b // q b}` is its rank: the number of smaller codes that satisfy `q`.
* A function on such a subtype is the list of digits of one number, read at the rank.
* A set with fewer than `J` elements is a mask, and the masks are the iterates of `Enum.next`.
* An assignment `{i // q i} → Bool` is the list of bits of one number, read at the rank.
-/

namespace TransposeBase.Pseudo.Code

open Finset

/-! ### Digits -/

/-- The digit of `k` in base `G` at position `i`. -/
def dig (G k i : ℕ) : ℕ := k / G ^ i % G

theorem dig_lt {G : ℕ} (hG : 0 < G) (k i : ℕ) : dig G k i < G := Nat.mod_lt _ hG

/-- The first `Q` digits of `k` in base `G`. -/
def wordOf {G : ℕ} (hG : 0 < G) (Q k : ℕ) : Fin Q → Fin G :=
  fun i => ⟨dig G k i, dig_lt hG k i⟩

@[simp] theorem wordOf_val {G : ℕ} (hG : 0 < G) (Q k : ℕ) (i : Fin Q) :
    (wordOf hG Q k i : ℕ) = k / G ^ (i : ℕ) % G := rfl

/-- The number with the digits `u`, the digit at position `0` being the lowest. -/
def wordIdx {G Q : ℕ} (u : Fin Q → Fin G) : ℕ := ∑ i, (u i : ℕ) * G ^ (i : ℕ)

theorem wordIdx_eq_equiv {G Q : ℕ} (u : Fin Q → Fin G) :
    wordIdx u = (finFunctionFinEquiv u : ℕ) := rfl

theorem wordIdx_lt {G Q : ℕ} (u : Fin Q → Fin G) : wordIdx u < G ^ Q :=
  (finFunctionFinEquiv u).2

/-- Reading the digits of `k < G ^ Q` is the inverse of `finFunctionFinEquiv`. -/
theorem wordOf_eq_symm {G Q k : ℕ} (hG : 0 < G) (hk : k < G ^ Q) :
    wordOf hG Q k = finFunctionFinEquiv.symm ⟨k, hk⟩ := rfl

theorem wordOf_wordIdx {G Q : ℕ} (hG : 0 < G) (u : Fin Q → Fin G) : wordOf hG Q (wordIdx u) = u := by
  rw [wordOf_eq_symm hG (wordIdx_lt u)]
  exact finFunctionFinEquiv.symm_apply_apply u

theorem wordIdx_wordOf {G Q k : ℕ} (hG : 0 < G) (hk : k < G ^ Q) : wordIdx (wordOf hG Q k) = k := by
  rw [wordOf_eq_symm hG hk, wordIdx_eq_equiv, Equiv.apply_symm_apply]

/-- A product over words is a product over the numbers below `G ^ Q`, decoded by their digits. -/
@[to_additive /-- A sum over words is a sum over the numbers below `G ^ Q`, decoded by their digits. -/]
theorem prod_word {M : Type*} [CommMonoid M] {G : ℕ} (hG : 0 < G) (Q : ℕ) (f : (Fin Q → Fin G) → M) :
    ∏ u : Fin Q → Fin G, f u = ∏ k ∈ range (G ^ Q), f (wordOf hG Q k) := by
  rw [Finset.prod_range (fun k => f (wordOf hG Q k))]
  exact ((finFunctionFinEquiv (m := G) (n := Q)).symm.prod_comp f).symm

/-- `prod_word` for the alphabet `Fin (N + 1)`, where the base is always positive. -/
@[to_additive /-- `sum_word` for the alphabet `Fin (N + 1)`, where the base is always positive. -/]
theorem prod_word_succ {M : Type*} [CommMonoid M] (N Q : ℕ) (f : (Fin Q → Fin (N + 1)) → M) :
    ∏ u : Fin Q → Fin (N + 1), f u = ∏ k ∈ range ((N + 1) ^ Q), f (wordOf (Nat.succ_pos N) Q k) :=
  prod_word (Nat.succ_pos N) Q f

/-! ### Sums over `Fin n` -/

/-- A product over `Fin n` is a product over `range n`, with no dependent summand. -/
@[to_additive /-- A sum over `Fin n` is a sum over `range n`, with no dependent summand. -/]
theorem prod_fin_eq_range {M : Type*} [CommMonoid M] (n : ℕ) (f : Fin n → M) :
    ∏ i : Fin n, f i = ∏ k ∈ range n, if h : k < n then f ⟨k, h⟩ else 1 := by
  rw [Finset.prod_range (fun k => if h : k < n then f ⟨k, h⟩ else 1)]
  exact Finset.prod_congr rfl fun i _ => by simp

section Rank

variable (p : ℕ → Prop) [DecidablePred p] (n : ℕ)

/-- The elements of `filter p (range n)` are counted by `Nat.count p n`. -/
theorem card_filter_range : ((range n).filter p).card = Nat.count p n :=
  (Nat.count_eq_card_filter_range p n).symm

theorem count_lt_of_mem {x : ℕ} (hx : x ∈ (range n).filter p) : Nat.count p x < Nat.count p n := by
  rw [Finset.mem_filter, Finset.mem_range] at hx
  exact Nat.count_strict_mono hx.2 hx.1

theorem count_injOn : Set.InjOn (Nat.count p) ((range n).filter p : Finset ℕ) := by
  intro x hx y hy h
  rw [Finset.mem_coe, Finset.mem_filter] at hx hy
  exact Nat.count_injective hx.2 hy.2 h

/-- The rank sends the filtered range onto `range (Nat.count p n)`. -/
theorem image_count : ((range n).filter p).image (Nat.count p) = range (Nat.count p n) := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (count_lt_of_mem p n hx)
  · rw [Finset.card_image_of_injOn (count_injOn p n), card_range, card_filter_range]

/-- `Nat.count` up to `x` reads the predicate only below `x`. -/
theorem count_congr {p' : ℕ → Prop} [DecidablePred p'] {x : ℕ} (h : ∀ k < x, p k ↔ p' k) :
    Nat.count p x = Nat.count p' x := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  exact Finset.filter_congr fun k hk => h k (Finset.mem_range.mp hk)

end Rank

section Subtype

variable {α : Type*} {n : ℕ} (code : α ≃ Fin n) (q : α → Prop) [DecidablePred q]

/-- The predicate `q` on codes. A number that is not a code does not satisfy it. -/
abbrev predOf : ℕ → Prop := fun k => ∃ h : k < n, q (code.symm ⟨k, h⟩)

/-- The rank of `b`: the number of smaller codes whose element satisfies `q`. -/
def rankOf (b : α) : ℕ := Nat.count (predOf code q) (code b)

/-- The number of elements that satisfy `q`, counted over all codes. -/
def excCard : ℕ := Nat.count (predOf code q) n

omit [DecidablePred q] in
theorem predOf_code (b : α) : predOf code q (code b) ↔ q b := by
  simp [predOf]

theorem rankOf_lt {b : α} (hb : q b) : rankOf code q b < excCard code q :=
  Nat.count_strict_mono ((predOf_code code q b).mpr hb) (code b).2

theorem rankOf_injOn {b b' : α} (hb : q b) (hb' : q b') (h : rankOf code q b = rankOf code q b') :
    b = b' := by
  have := Nat.count_injective ((predOf_code code q b).mpr hb) ((predOf_code code q b').mpr hb') h
  exact code.injective (Fin.ext this)

theorem exists_rankOf_eq {r : ℕ} (hr : r < excCard code q) : ∃ b, q b ∧ rankOf code q b = r := by
  have hr' : r ∈ ((range n).filter (predOf code q)).image (Nat.count (predOf code q)) := by
    rw [image_count]
    exact Finset.mem_range.mpr hr
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr'
  obtain ⟨-, h, hq⟩ := Finset.mem_filter.mp hx
  exact ⟨code.symm ⟨x, h⟩, hq, by simp [rankOf]⟩

/-- The subtype of `q`, numbered by rank. -/
noncomputable def excEquiv : {b // q b} ≃ Fin (excCard code q) :=
  Equiv.ofBijective (fun b => ⟨rankOf code q b.1, rankOf_lt code q b.2⟩) <| by
    constructor
    · intro b b' h
      exact Subtype.ext (rankOf_injOn code q b.2 b'.2 (congrArg Fin.val h))
    · rintro ⟨r, hr⟩
      obtain ⟨b, hb, rfl⟩ := exists_rankOf_eq code q hr
      exact ⟨⟨b, hb⟩, rfl⟩

theorem excCard_eq_fintype_card [Fintype {b // q b}] : excCard code q = Fintype.card {b // q b} := by
  simpa using (Fintype.card_congr (excEquiv code q)).symm

/-- The rank agrees with the count of any number predicate that agrees with `q` on the codes. -/
theorem rankOf_eq_count {p : ℕ → Prop} [DecidablePred p] (hp : ∀ b, p (code b) ↔ q b) (b : α) :
    rankOf code q b = Nat.count p (code b) := by
  refine count_congr _ fun k hk => ?_
  have hkn : k < n := hk.trans (code b).2
  have := hp (code.symm ⟨k, hkn⟩)
  simp only [Equiv.apply_symm_apply] at this
  exact ⟨fun ⟨_, h⟩ => this.mpr h, fun h => ⟨hkn, this.mp h⟩⟩

theorem excCard_eq_count {p : ℕ → Prop} [DecidablePred p] (hp : ∀ b, p (code b) ↔ q b) :
    excCard code q = Nat.count p n := by
  refine count_congr _ fun k hkn => ?_
  have := hp (code.symm ⟨k, hkn⟩)
  simp only [Equiv.apply_symm_apply] at this
  exact ⟨fun ⟨_, h⟩ => this.mpr h, fun h => ⟨hkn, this.mp h⟩⟩

/-- A product over the functions from the subtype to `Fin m`. The number `k` is decoded by reading its digit
in base `m` at the rank of each element. -/
@[to_additive /-- A sum over the functions from the subtype to `Fin m`. The number `k` is decoded by reading
its digit in base `m` at the rank of each element. -/]
theorem prod_exc_fun {M : Type*} [CommMonoid M] [Fintype {b // q b}] [DecidableEq {b // q b}]
    {m : ℕ} (hm : 0 < m) (F : ({b // q b} → Fin m) → M) :
    ∏ ρ : {b // q b} → Fin m, F ρ =
      ∏ k ∈ range (m ^ excCard code q),
        F (fun b => ⟨dig m k (rankOf code q b.1), dig_lt hm _ _⟩) := by
  rw [← (((excEquiv code q).arrowCongr (Equiv.refl (Fin m))).symm.prod_comp F),
    prod_word hm (excCard code q)]
  rfl

/-- The digit in base `2` is the bit. -/
theorem finTwoEquiv_dig (k r : ℕ) (h : dig 2 k r < 2) :
    finTwoEquiv ⟨dig 2 k r, h⟩ = k.testBit r := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  unfold dig at h ⊢
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ r) with h0 | h0 <;> simp [h0, finTwoEquiv]

/-- A product over the assignments of the subtype. The number `k` is decoded by reading its bit at the rank
of each element. -/
@[to_additive /-- A sum over the assignments of the subtype. The number `k` is decoded by reading its bit at
the rank of each element. -/]
theorem prod_exc_bool {M : Type*} [CommMonoid M] [Fintype {b // q b}] [DecidableEq {b // q b}]
    (F : ({b // q b} → Bool) → M) :
    ∏ v : {b // q b} → Bool, F v =
      ∏ k ∈ range (2 ^ excCard code q), F (fun b => k.testBit (rankOf code q b.1)) := by
  rw [← (((Equiv.refl {b // q b}).arrowCongr finTwoEquiv).prod_comp F),
    prod_exc_fun code q (by norm_num : 0 < 2)]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  funext b
  exact finTwoEquiv_dig k _ _

/-- `prod_exc_bool` with the rank written by a number predicate `p` that agrees with `q` on the codes. -/
@[to_additive /-- `sum_exc_bool` with the rank written by a number predicate `p` that agrees with `q` on the
codes. -/]
theorem prod_exc_bool_count {M : Type*} [CommMonoid M] [Fintype {b // q b}] [DecidableEq {b // q b}]
    {p : ℕ → Prop} [DecidablePred p] (hp : ∀ b, p (code b) ↔ q b) (F : ({b // q b} → Bool) → M) :
    ∏ v : {b // q b} → Bool, F v =
      ∏ k ∈ range (2 ^ Nat.count p n), F (fun b => k.testBit (Nat.count p (code b.1))) := by
  rw [prod_exc_bool code q F, excCard_eq_count code q hp]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  funext b
  rw [rankOf_eq_count code q hp]

end Subtype

section Masks

open Enum

variable {α : Type*} [Fintype α]

/-- The sets of fewer than `J` elements of `α`. For `α = Cell Q A` this is `fewCells J` by `rfl`. -/
def fewSets (α : Type*) [Fintype α] (J : ℕ) : Finset (Finset α) :=
  Finset.univ.filter (fun S => S.card < J)

variable {N : ℕ} (code : α ≃ Fin N)

/-- The set of elements of `α` whose code is a set bit of `x`. -/
def setOfMask (x : ℕ) : Finset α := Finset.univ.filter (fun a => x.testBit (code a) = true)

@[simp] theorem mem_setOfMask {x : ℕ} {a : α} : a ∈ setOfMask code x ↔ x.testBit (code a) = true := by
  simp [setOfMask]

/-- The set of a mask is the set of the codes, moved back to `α`. -/
theorem setOfMask_mask_eq (S' : Finset (Fin N)) :
    setOfMask code (mask S') = S'.map code.symm.toEmbedding := by
  ext a
  rw [mem_setOfMask, testBit_mask, Finset.mem_map_equiv, Equiv.symm_symm]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(code a).2, h⟩⟩

omit [Fintype α] in
theorem map_symm_map (S : Finset α) : (S.map code.toEmbedding).map code.symm.toEmbedding = S := by
  ext a
  simp

/-- A product over the sets of `α` is a product over the sets of codes. -/
@[to_additive /-- A sum over the sets of `α` is a sum over the sets of codes. -/]
theorem prod_fewSets {M : Type*} [CommMonoid M] (J : ℕ) (F : Finset α → M) :
    ∏ S ∈ fewSets α J, F S =
      ∏ S' ∈ Finset.univ.filter (fun S' : Finset (Fin N) => S'.card < J),
        F (S'.map code.symm.toEmbedding) := by
  refine Finset.prod_equiv code.finsetCongr (fun S => ?_) (fun S _ => ?_)
  · simp [fewSets]
  · exact congrArg F (map_symm_map code S).symm

include code in
theorem card_fewSets (J : ℕ) :
    (fewSets α J).card = (Finset.univ.filter (fun S' : Finset (Fin N) => S'.card < J)).card := by
  have := sum_fewSets code (M := ℕ) J (fun _ => 1)
  simpa using this

/-- A sum over the sets of fewer than `J` elements of `α` is a sum over iterates of `Enum.next`, when `G` is a
summand on numbers that decodes masks, and it vanishes from `2 ^ N` on. -/
theorem sum_it_eq_fewSets {M : Type*} [AddCommMonoid M] {J n : ℕ} (hJ : 1 ≤ J)
    (hn : (fewSets α J).card ≤ n) (F : Finset α → M) (G : ℕ → M)
    (hG0 : ∀ x, 2 ^ N ≤ x → G x = 0)
    (hG : ∀ S' : Finset (Fin N), G (mask S') = F (S'.map code.symm.toEmbedding)) :
    ∑ k ∈ range n, G (it N J k) = ∑ S ∈ fewSets α J, F S := by
  rw [sum_it_eq hJ (by rwa [← card_fewSets code]) G hG0, sum_fewSets code]
  exact Finset.sum_congr rfl fun S' _ => hG S'

/-- `sum_it_eq_fewSets` with the decoding written out: the summand at `x` reads the set with `setOfMask`. -/
theorem sum_it_setOfMask {M : Type*} [AddCommMonoid M] {J n : ℕ} (hJ : 1 ≤ J)
    (hn : (fewSets α J).card ≤ n) (F : Finset α → M) :
    ∑ k ∈ range n, (if it N J k < 2 ^ N then F (setOfMask code (it N J k)) else 0) =
      ∑ S ∈ fewSets α J, F S := by
  refine sum_it_eq_fewSets code hJ hn F
    (fun x => if x < 2 ^ N then F (setOfMask code x) else 0) (fun x hx => ?_) (fun S' => ?_)
  · simp [not_lt.mpr hx]
  · simp [mask_lt S', setOfMask_mask_eq]

end Masks

section SumCode

/-- The code of two copies of `Fin m`: the first copy keeps its number, and the second is shifted by `m`. -/
def sumCode (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (two_mul m).symm)

@[simp] theorem sumCode_inl (m : ℕ) (e : Fin m) : (sumCode m (Sum.inl e) : ℕ) = e := rfl

@[simp] theorem sumCode_inr (m : ℕ) (e : Fin m) : (sumCode m (Sum.inr e) : ℕ) = m + e := rfl

variable {E : Type*} {m : ℕ} (c : E ≃ Fin m)

/-- The code of two copies of a type with code `c`. -/
def sumCodeOf : E ⊕ E ≃ Fin (2 * m) := (Equiv.sumCongr c c).trans (sumCode m)

@[simp] theorem sumCodeOf_inl (e : E) : (sumCodeOf c (Sum.inl e) : ℕ) = c e := rfl

@[simp] theorem sumCodeOf_inr (e : E) : (sumCodeOf c (Sum.inr e) : ℕ) = m + c e := rfl

end SumCode

end TransposeBase.Pseudo.Code
