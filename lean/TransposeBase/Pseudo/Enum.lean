import Mathlib

/-!
# Enumerating masks with few bits, and Kronecker extraction

These are specifications over `ℕ`, not programs.

* `next N J` steps from one mask with fewer than `J` set bits to the next one. So a sum over the sets of
  fewer than `J` elements of `Fin N` is a sum over the iterates of `next N J` from `0`.
* `lowbit` and `pop` have formulas that read only the bits of the word.
* The value of a polynomial with small coefficients at `2 ^ B` holds its coefficients in fields of `B` bits.
* The Lagrange basis on the grid `0, ..., N`, multiplied by `N !`, has integer coefficients. They come from
  `∏ j ≠ b, (X + j)` and `Nat.choose N b`, with an explicit sign.
-/

namespace TransposeBase.Pseudo.Enum

open Finset Polynomial

/-! ### Set bits -/

/-- The number of set bits. -/
def pop (x : ℕ) : ℕ := (Nat.bitIndices x).length

/-- The value of the least set bit. The value at `0` is `1`, and it is not used. -/
def lowbit (x : ℕ) : ℕ := 2 ^ (Nat.bitIndices x).headD 0

@[simp] theorem pop_zero : pop 0 = 0 := by simp [pop]

@[simp] theorem pop_two_mul (a : ℕ) : pop (2 * a) = pop a := by simp [pop]

@[simp] theorem pop_two_mul_add_one (a : ℕ) : pop (2 * a + 1) = pop a + 1 := by simp [pop]

theorem eq_zero_of_pop_eq_zero {x : ℕ} (h : pop x = 0) : x = 0 := by
  have hnil : Nat.bitIndices x = [] := List.length_eq_zero_iff.mp h
  have hsum := Nat.sum_map_two_pow_bitIndices x
  rw [hnil] at hsum
  simpa using hsum.symm

theorem lowbit_pos (x : ℕ) : 0 < lowbit x := by
  unfold lowbit
  positivity

@[simp] theorem lowbit_two_mul_add_one (a : ℕ) : lowbit (2 * a + 1) = 1 := by simp [lowbit]

theorem lowbit_two_mul {a : ℕ} (ha : 0 < a) : lowbit (2 * a) = 2 * lowbit a := by
  cases h : Nat.bitIndices a with
  | nil =>
    have : pop a = 0 := by simp [pop, h]
    have := eq_zero_of_pop_eq_zero this
    omega
  | cons i l =>
    simp [lowbit, h, pow_succ]
    ring

/-- Adding one sets at most one new bit. -/
theorem pop_succ_le (x : ℕ) : pop (x + 1) ≤ pop x + 1 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' x
    · rw [pop_two_mul, pop_two_mul_add_one]
    · have h2 : 2 * a + 1 + 1 = 2 * (a + 1) := by ring
      rw [h2, pop_two_mul, pop_two_mul_add_one]
      have := ih a (by omega)
      omega

/-- Adding the least set bit does not raise the number of set bits. -/
theorem pop_add_lowbit_le {x : ℕ} (hx : 0 < x) : pop (x + lowbit x) ≤ pop x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' x
    · have ha : 0 < a := by omega
      rw [lowbit_two_mul ha, ← mul_add, pop_two_mul, pop_two_mul]
      exact ih a (by omega) ha
    · rw [lowbit_two_mul_add_one, pop_two_mul_add_one]
      have h2 : 2 * a + 1 + 1 = 2 * (a + 1) := by ring
      rw [h2, pop_two_mul]
      exact pop_succ_le a

/-- A number above `x` with at most as many set bits as `x` is at least `x + lowbit x`. -/
theorem add_lowbit_le {x y : ℕ} (hx : 0 < x) (hxy : x < y) (hp : pop y ≤ pop x) :
    x + lowbit x ≤ y := by
  induction x using Nat.strong_induction_on generalizing y with
  | _ x ih =>
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' x
    · have ha : 0 < a := by omega
      rw [lowbit_two_mul ha, pop_two_mul] at *
      obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' y
      · rw [pop_two_mul] at hp
        have := ih a (by omega) ha (y := b) (by omega) hp
        omega
      · rw [pop_two_mul_add_one] at hp
        have hab : a ≠ b := by
          rintro rfl
          omega
        have := ih a (by omega) ha (y := b) (by omega) (by omega)
        omega
    · rw [lowbit_two_mul_add_one]
      omega

/-! ### The next mask -/

/-- The step of the enumeration. The sentinel `2 ^ N` is used only for `J ≤ 1`, where `0` is the only
mask. -/
def next (N J x : ℕ) : ℕ :=
  if pop x + 1 < J then x + 1 else if x = 0 then 2 ^ N else x + lowbit x

/-- The `k`-th iterate of `next` from `0`. -/
def it (N J k : ℕ) : ℕ := (next N J)^[k] 0

theorem lt_next (N J x : ℕ) : x < next N J x := by
  unfold next
  split_ifs with h1 h2
  · omega
  · subst h2
    positivity
  · have := lowbit_pos x
    omega

theorem pop_next_lt_or {N J x : ℕ} (hx : pop x < J) :
    pop (next N J x) < J ∨ 2 ^ N ≤ next N J x := by
  unfold next
  split_ifs with h1 h2
  · left
    have := pop_succ_le x
    omega
  · right
    exact le_rfl
  · left
    have := pop_add_lowbit_le (Nat.pos_of_ne_zero h2)
    omega

/-- No mask lies strictly between `x` and `next N J x`. -/
theorem next_le {N J x y : ℕ} (hxy : x < y) (hy : pop y < J) : next N J x ≤ y := by
  unfold next
  split_ifs with h1 h2
  · omega
  · subst h2
    have : pop y = 0 := by
      simp only [pop_zero] at h1
      omega
    have := eq_zero_of_pop_eq_zero this
    omega
  · exact add_lowbit_le (Nat.pos_of_ne_zero h2) hxy (by omega)

@[simp] theorem it_zero (N J : ℕ) : it N J 0 = 0 := rfl

theorem it_succ (N J k : ℕ) : it N J (k + 1) = next N J (it N J k) :=
  Function.iterate_succ_apply' _ _ _

/-- The iterates are strictly increasing, so they are distinct. -/
theorem it_strictMono (N J : ℕ) : StrictMono (it N J) :=
  strictMono_nat_of_lt_succ fun k => by
    rw [it_succ]
    exact lt_next N J _

theorem it_injective (N J : ℕ) : Function.Injective (it N J) := (it_strictMono N J).injective

/-- Each iterate has fewer than `J` set bits, or it is at least `2 ^ N`. -/
theorem pop_it_lt_or {N J : ℕ} (hJ : 1 ≤ J) (k : ℕ) :
    pop (it N J k) < J ∨ 2 ^ N ≤ it N J k := by
  induction k with
  | zero =>
    left
    rw [it_zero, pop_zero]
    omega
  | succ k ih =>
    rw [it_succ]
    rcases ih with h | h
    · exact pop_next_lt_or h
    · right
      exact h.trans (lt_next N J _).le

/-- Each number with fewer than `J` set bits is an iterate. -/
theorem exists_it_eq {N J y : ℕ} (hy : pop y < J) : ∃ k, it N J k = y := by
  classical
  have hex : ∃ k, y ≤ it N J k := ⟨y, (it_strictMono N J).le_apply⟩
  refine ⟨Nat.find hex, le_antisymm ?_ (Nat.find_spec hex)⟩
  rcases hk : Nat.find hex with _ | k
  · have := Nat.find_spec hex
    rw [hk] at this
    simp only [it_zero] at this ⊢
    omega
  · have hlt : it N J k < y := by
      have := Nat.find_min hex (m := k) (by omega)
      omega
    rw [it_succ]
    exact next_le hlt hy

/-! ### Masks of sets -/

/-- The mask of a set. -/
def mask {N : ℕ} (S : Finset (Fin N)) : ℕ := ∑ i ∈ S, 2 ^ (i : ℕ)

theorem mask_eq_sum_map {N : ℕ} (S : Finset (Fin N)) :
    mask S = ∑ i ∈ S.map Fin.valEmbedding, 2 ^ i := by
  simp [mask]

theorem toFinset_bitIndices_mask {N : ℕ} (S : Finset (Fin N)) :
    (Nat.bitIndices (mask S)).toFinset = S.map Fin.valEmbedding := by
  rw [mask_eq_sum_map]
  exact Finset.toFinset_bitIndices_sum_two_pow _

/-- The bits of a mask are the elements of the set. -/
theorem testBit_mask {N : ℕ} (S : Finset (Fin N)) (i : ℕ) :
    (mask S).testBit i = true ↔ ∃ h : i < N, (⟨i, h⟩ : Fin N) ∈ S := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, toFinset_bitIndices_mask]
  simp only [Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨h, hi⟩
    exact ⟨_, hi, rfl⟩

theorem pop_mask {N : ℕ} (S : Finset (Fin N)) : pop (mask S) = S.card := by
  have h := congrArg Finset.card (toFinset_bitIndices_mask S)
  rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup, Finset.card_map] at h
  exact h

theorem mask_lt {N : ℕ} (S : Finset (Fin N)) : mask S < 2 ^ N := by
  have hle : ∑ i ∈ S.map Fin.valEmbedding, 2 ^ i ≤ ∑ i ∈ range N, 2 ^ i := by
    apply Finset.sum_le_sum_of_subset
    intro i hi
    simp only [Finset.mem_map, Fin.valEmbedding_apply] at hi
    obtain ⟨a, _, rfl⟩ := hi
    exact Finset.mem_range.mpr a.2
  have hgeom : ∑ i ∈ range N, 2 ^ i < 2 ^ N := by
    have := Nat.geomSum_lt (m := 2) (n := N) (s := range N) le_rfl (by simp)
    exact this
  rw [mask_eq_sum_map]
  omega

theorem mask_injective (N : ℕ) : Function.Injective (mask (N := N)) := by
  intro S T h
  have := toFinset_bitIndices_mask S
  rw [h, toFinset_bitIndices_mask T] at this
  exact (Finset.map_injective _ this).symm

theorem exists_mask_eq {N x : ℕ} (hx : x < 2 ^ N) : ∃ S : Finset (Fin N), mask S = x := by
  refine ⟨Finset.univ.filter fun i : Fin N => x.testBit i = true, ?_⟩
  have hmap : (Finset.univ.filter fun i : Fin N => x.testBit i = true).map Fin.valEmbedding =
      (Nat.bitIndices x).toFinset := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, List.mem_toFinset, Nat.mem_bitIndices]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hi
      have hlt : i < N := by
        by_contra hge
        have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hge)))
        simp_all
      exact ⟨⟨i, hlt⟩, hi, rfl⟩
  rw [mask_eq_sum_map, hmap]
  exact Finset.sum_toFinset_bitIndices_two_pow x

/-! ### The sum over the iterates -/

/-- A sum over the sets of fewer than `J` elements of `Fin N` is a sum over the iterates of `next`, for any
number `n` of iterates that is at least the number of sets, when `g` vanishes from `2 ^ N` on. -/
theorem sum_it_eq {M : Type*} [AddCommMonoid M] {N J n : ℕ} (hJ : 1 ≤ J)
    (hn : (Finset.univ.filter fun S : Finset (Fin N) => S.card < J).card ≤ n)
    (g : ℕ → M) (hg : ∀ x, 2 ^ N ≤ x → g x = 0) :
    ∑ k ∈ range n, g (it N J k) =
      ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin N) => S.card < J), g (mask S) := by
  classical
  set F := Finset.univ.filter fun S : Finset (Fin N) => S.card < J with hF
  set V := F.image mask with hV
  have hVcard : V.card = F.card := Finset.card_image_of_injective _ (mask_injective N)
  have hmemV : ∀ x, x ∈ V ↔ x < 2 ^ N ∧ pop x < J := by
    intro x
    simp only [hV, hF, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨mask_lt S, by rwa [pop_mask]⟩
    · rintro ⟨hx, hp⟩
      obtain ⟨S, rfl⟩ := exists_mask_eq hx
      exact ⟨S, by rwa [pop_mask] at hp, rfl⟩
  have hit : ∀ k, it N J k < 2 ^ N → it N J k ∈ V := by
    intro k hk
    rw [hmemV]
    refine ⟨hk, ?_⟩
    rcases pop_it_lt_or (N := N) hJ k with h | h
    · exact h
    · omega
  set A := (range n).filter fun k => it N J k < 2 ^ N with hA
  have himage : A.image (it N J) = V := by
    ext x
    simp only [Finset.mem_image, hA, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨k, ⟨_, hk⟩, rfl⟩
      exact hit k hk
    · intro hx
      obtain ⟨hxN, hxp⟩ := (hmemV x).mp hx
      obtain ⟨k, rfl⟩ := exists_it_eq (N := N) hxp
      refine ⟨k, ⟨?_, hxN⟩, rfl⟩
      have hsub : (range (k + 1)).image (it N J) ⊆ V := by
        intro y hy
        simp only [Finset.mem_image, Finset.mem_range] at hy
        obtain ⟨l, hl, rfl⟩ := hy
        apply hit
        exact lt_of_le_of_lt ((it_strictMono N J).monotone (by omega)) hxN
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ (it_injective N J), Finset.card_range, hVcard] at hc
      omega
  calc ∑ k ∈ range n, g (it N J k)
      = ∑ k ∈ A, g (it N J k) := by
        rw [hA, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        split_ifs with h
        · rfl
        · exact hg _ (not_lt.mp h)
    _ = ∑ x ∈ V, g x := by
        rw [← himage, Finset.sum_image (fun a _ b _ h => it_injective N J h)]
    _ = ∑ S ∈ F, g (mask S) := by
        rw [hV, Finset.sum_image (fun a _ b _ h => mask_injective N h)]

/-! ### Formulas that read the bits -/

theorem testBit_two_mul_zero (a : ℕ) : (2 * a).testBit 0 = false := by
  simp [Nat.testBit_zero]

theorem testBit_two_mul_add_one_zero (a : ℕ) : (2 * a + 1).testBit 0 = true := by
  simp [Nat.testBit_zero]

theorem testBit_two_mul_succ (a i : ℕ) : (2 * a).testBit (i + 1) = a.testBit i := by
  rw [Nat.testBit_succ]
  congr 1
  omega

theorem testBit_two_mul_add_one_succ (a i : ℕ) : (2 * a + 1).testBit (i + 1) = a.testBit i := by
  rw [Nat.testBit_succ]
  congr 1
  omega

/-- The number of set bits, read from the bits. -/
theorem pop_eq_sum {B x : ℕ} (hx : x < 2 ^ B) : pop x = ∑ i ∈ range B, (x.testBit i).toNat := by
  induction B generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    simp [this]
  | succ B ih =>
    rw [Finset.sum_range_succ']
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' x
    · have ha : a < 2 ^ B := by rw [pow_succ] at hx; omega
      simp only [testBit_two_mul_succ, testBit_two_mul_zero, pop_two_mul, Bool.toNat_false, add_zero]
      exact ih ha
    · have ha : a < 2 ^ B := by rw [pow_succ] at hx; omega
      simp only [testBit_two_mul_add_one_succ, testBit_two_mul_add_one_zero, pop_two_mul_add_one,
        Bool.toNat_true]
      rw [ih ha]

/-- The least set bit, read from the bits. The factor `2 ^ i` survives only at the first set bit. -/
theorem lowbit_eq_sum {B x : ℕ} (hx0 : 0 < x) (hx : x < 2 ^ B) :
    lowbit x = ∑ i ∈ range B,
      (x.testBit i).toNat * (∏ j ∈ range i, (1 - (x.testBit j).toNat)) * 2 ^ i := by
  induction B generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    omega
  | succ B ih =>
    rw [Finset.sum_range_succ']
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' x
    · have ha : a < 2 ^ B := by rw [pow_succ] at hx; omega
      have ha0 : 0 < a := by omega
      simp only [Finset.prod_range_succ', testBit_two_mul_succ, testBit_two_mul_zero,
        Bool.toNat_false, Nat.sub_zero, mul_one, zero_mul, add_zero]
      rw [lowbit_two_mul ha0, ih ha0 ha, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [Finset.prod_range_succ', testBit_two_mul_add_one_zero, Bool.toNat_true,
        lowbit_two_mul_add_one]
      simp

/-! ### Kronecker extraction -/

/-- The value at `2 ^ B` holds the coefficients in fields of `B` bits, when each is below `2 ^ B`. -/
theorem eval_two_pow_field (p : ℕ[X]) {B : ℕ} (h : ∀ i, p.coeff i < 2 ^ B) (e : ℕ) :
    (p.eval (2 ^ B) / 2 ^ (B * e)) % 2 ^ B = p.coeff e := by
  have hsplit : ∀ q : ℕ[X], q.eval (2 ^ B) = 2 ^ B * q.divX.eval (2 ^ B) + q.coeff 0 := by
    intro q
    conv_lhs => rw [← Polynomial.divX_mul_X_add q]
    simp [mul_comm]
  induction e generalizing p with
  | zero =>
    rw [mul_zero, pow_zero, Nat.div_one, hsplit, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (h 0)
  | succ e ih =>
    have hd : ∀ i, p.divX.coeff i < 2 ^ B := by
      intro i
      rw [Polynomial.coeff_divX]
      exact h _
    have hdiv : p.eval (2 ^ B) / 2 ^ B = p.divX.eval (2 ^ B) := by
      rw [hsplit, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt (h 0), add_zero]
    rw [Nat.mul_succ, pow_add, mul_comm (2 ^ (B * e)), ← Nat.div_div_eq_div_mul, hdiv, ih _ hd,
      Polynomial.coeff_divX]

/-- A coefficient over `ℕ` is at most the value at `1`, which is the sum of all coefficients. -/
theorem coeff_le_eval_one (p : ℕ[X]) (e : ℕ) : p.coeff e ≤ p.eval 1 := by
  by_cases he : e ≤ p.natDegree
  · rw [Polynomial.eval_eq_sum_range]
    simp only [one_pow, mul_one]
    exact Finset.single_le_sum (f := fun i => p.coeff i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le he))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp he)]
    exact Nat.zero_le _

/-- Each coefficient of `∏ j ∈ s, (X + f j)` is at most `∏ j ∈ s, (1 + f j)`. -/
theorem coeff_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (e : ℕ) :
    (∏ j ∈ s, (X + C (f j))).coeff e ≤ ∏ j ∈ s, (1 + f j) := by
  have := coeff_le_eval_one (∏ j ∈ s, (X + C (f j))) e
  simpa [Polynomial.eval_prod] using this

/-- Kronecker extraction for a product. The product is a single number. -/
theorem prod_field {ι : Type*} (s : Finset ι) (f : ι → ℕ) {B : ℕ}
    (hB : ∏ j ∈ s, (1 + f j) < 2 ^ B) (e : ℕ) :
    ((∏ j ∈ s, (2 ^ B + f j)) / 2 ^ (B * e)) % 2 ^ B = (∏ j ∈ s, (X + C (f j))).coeff e := by
  have h := eval_two_pow_field (∏ j ∈ s, (X + C (f j))) (B := B)
    (fun i => lt_of_le_of_lt (coeff_prod_le s f i) hB) e
  simpa [Polynomial.eval_prod] using h

/-- The coefficients of `(X + 1) ^ N` are the binomial coefficients. -/
theorem coeff_X_add_one_pow_nat (N e : ℕ) : (((X + 1) ^ N : ℕ[X])).coeff e = N.choose e := by
  simpa using Polynomial.coeff_X_add_one_pow ℕ N e

/-- Kronecker extraction for the binomial coefficients. -/
theorem choose_field {N B : ℕ} (hB : N < B) (e : ℕ) :
    ((2 ^ B + 1) ^ N / 2 ^ (B * e)) % 2 ^ B = N.choose e := by
  have hlt : ∀ i, (((X + 1) ^ N : ℕ[X])).coeff i < 2 ^ B := by
    intro i
    rw [coeff_X_add_one_pow_nat]
    exact lt_of_le_of_lt (Nat.choose_le_two_pow N i) (Nat.pow_lt_pow_right (by norm_num) hB)
  have h := eval_two_pow_field ((X + 1) ^ N : ℕ[X]) hlt e
  rw [coeff_X_add_one_pow_nat] at h
  simpa using h

section Lagrange

variable {k : Type*} [Field k]

/-- Replacing `X + a` by `X - a` multiplies the coefficient of `X ^ e` by `(-1) ^ (card + e)`. -/
theorem coeff_prod_X_sub {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (e : ℕ) :
    (∏ j ∈ s, (X - C ((f j : ℕ) : k))).coeff e =
      (-1) ^ (s.card + e) * (((∏ j ∈ s, (X + C (f j))).coeff e : ℕ) : k) := by
  induction s using Finset.induction_on generalizing e with
  | empty =>
    cases e with
    | zero => simp
    | succ e => simp [Polynomial.coeff_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    cases e with
    | zero =>
      simp only [sub_mul, add_mul, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, ih 0]
      push_cast
      ring
    | succ e =>
      simp only [sub_mul, add_mul, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, ih e, ih (e + 1)]
      push_cast
      ring

/-- The product `∏ j ≠ b, (b - j)` over `j ≤ N`, moved from `Fin` to `ℕ` and split at `b`. -/
theorem prod_erase_range (b m : ℕ) (h : ℕ → k) :
    ∏ j ∈ (range (b + 1 + m)).erase b, h j =
      (∏ j ∈ range b, h j) * ∏ i ∈ range m, h (b + 1 + i) := by
  induction m with
  | zero =>
    simp [Finset.range_add_one]
  | succ m ih =>
    rw [← add_assoc, Finset.range_add_one (n := b + 1 + m), Finset.erase_insert_of_ne (by omega),
      Finset.prod_insert (by simp), ih, Finset.prod_range_succ]
    ring

theorem prod_range_sub_self (b : ℕ) : ∏ j ∈ range b, ((b : k) - (j : k)) = (b.factorial : k) := by
  rw [← Finset.prod_range_reflect, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  apply Finset.prod_congr rfl
  intro j hj
  have hj' : j < b := Finset.mem_range.mp hj
  have : ((b - 1 - j : ℕ) : k) = (b : k) - 1 - j := by
    rw [show b - 1 - j = b - (1 + j) by omega, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [this]
  ring

theorem prod_range_sub_above (b m : ℕ) :
    ∏ i ∈ range m, ((b : k) - ((b + 1 + i : ℕ) : k)) = (-1) ^ m * (m.factorial : k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- The denominator of the Lagrange basis on the grid `0, ..., N`. -/
theorem prod_erase_grid (N : ℕ) (b : Fin (N + 1)) :
    ∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b, (((b : ℕ) : k) - ((j : ℕ) : k)) =
      (-1) ^ (N - (b : ℕ)) * ((b : ℕ).factorial : k) * ((N - (b : ℕ)).factorial : k) := by
  have hb : (b : ℕ) ≤ N := Nat.lt_succ_iff.mp b.2
  have hmap : ((Finset.univ : Finset (Fin (N + 1))).erase b).map Fin.valEmbedding =
      (range ((b : ℕ) + 1 + (N - (b : ℕ)))).erase (b : ℕ) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨fun h => ha (Fin.ext h), ?_⟩
      have := a.2
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨⟨i, by omega⟩, fun h => h1 (by rw [← h]), rfl⟩
  have hprod : ∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b, (((b : ℕ) : k) - ((j : ℕ) : k)) =
      ∏ j ∈ (range ((b : ℕ) + 1 + (N - (b : ℕ)))).erase (b : ℕ), (((b : ℕ) : k) - (j : k)) := by
    rw [← hmap, Finset.prod_map]
    rfl
  rw [hprod, prod_erase_range, prod_range_sub_self, prod_range_sub_above]
  ring

/-- The Lagrange basis over the grid `0, ..., N`, multiplied by `N !`, in natural numbers and a sign:
the coefficient of `X ^ e` is `(-1) ^ ((N - e) + (N - b))` times `Nat.choose N b` times the coefficient
of `X ^ e` in `∏ j ≠ b, (X + j)` over `ℕ`. -/
theorem factorial_mul_coeff_basis [CharZero k] (N e : ℕ) (b : Fin (N + 1)) :
    (N.factorial : k) *
        (Lagrange.basis Finset.univ (fun b : Fin (N + 1) => ((b : ℕ) : k)) b).coeff e =
      (-1) ^ (N - e + (N - (b : ℕ))) * (N.choose (b : ℕ) : k) *
        (((∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b,
            (X + C ((j : ℕ) : ℕ))).coeff e : ℕ) : k) := by
  have hb : (b : ℕ) ≤ N := Nat.lt_succ_iff.mp b.2
  have hcard : ((Finset.univ : Finset (Fin (N + 1))).erase b).card = N := by simp
  -- The basis is a constant times `∏ j ≠ b, (X - j)`.
  have hbasis : Lagrange.basis Finset.univ (fun b : Fin (N + 1) => ((b : ℕ) : k)) b =
      C (∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b, (((b : ℕ) : k) - ((j : ℕ) : k)))⁻¹ *
        ∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b, (X - C (((j : ℕ) : ℕ) : k)) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_inv_distrib]
  -- The sign of the coefficient, with `N + e` replaced by `N - e`.
  have hsign : ∀ e, (-1 : k) ^ (N + e) *
      (((∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b,
        (X + C ((j : ℕ) : ℕ))).coeff e : ℕ) : k) =
      (-1 : k) ^ (N - e) * (((∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b,
        (X + C ((j : ℕ) : ℕ))).coeff e : ℕ) : k) := by
    intro e
    by_cases he : e ≤ N
    · have hpar : N + e = (N - e) + 2 * e := by omega
      rw [hpar, pow_add, pow_mul]
      simp
    · have hdeg : (∏ j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b,
          (X + C ((j : ℕ) : ℕ))).natDegree ≤ N := by
        refine (Polynomial.natDegree_prod_le _ _).trans ?_
        calc _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin (N + 1))).erase b, 1 :=
              Finset.sum_le_sum fun j _ => (Polynomial.natDegree_X_add_C _).le
          _ = N := by simp
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (not_le.mp he))]
      simp
  have hN : (N.factorial : k) =
      (N.choose (b : ℕ) : k) * ((b : ℕ).factorial : k) * ((N - (b : ℕ)).factorial : k) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hb).symm
  have hb0 : ((b : ℕ).factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc0 : ((N - (b : ℕ)).factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs0 : (-1 : k) ^ (N - (b : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h1 : ((-1 : k) ^ (N - (b : ℕ))) * ((-1 : k) ^ (N - (b : ℕ))) = 1 := by
    rw [← mul_pow]
    simp
  -- `N !` divided by the denominator is a signed binomial coefficient.
  have hD : (N.factorial : k) * ((-1) ^ (N - (b : ℕ)) * ((b : ℕ).factorial : k) *
      ((N - (b : ℕ)).factorial : k))⁻¹ = (-1) ^ (N - (b : ℕ)) * (N.choose (b : ℕ) : k) := by
    rw [mul_inv_eq_iff_eq_mul₀ (mul_ne_zero (mul_ne_zero hs0 hb0) hc0), hN]
    linear_combination (-(N.choose (b : ℕ) : k) * ((b : ℕ).factorial : k) *
      ((N - (b : ℕ)).factorial : k)) * h1
  rw [hbasis, Polynomial.coeff_C_mul, prod_erase_grid,
    coeff_prod_X_sub ((Finset.univ : Finset (Fin (N + 1))).erase b) (fun j => (j : ℕ)) e, hcard,
    hsign e, ← mul_assoc, hD, pow_add]
  ring

end Lagrange

end TransposeBase.Pseudo.Enum
