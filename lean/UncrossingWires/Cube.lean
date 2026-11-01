import Mathlib

/-!
# Finite families of functions on `ℕ`

`cube n S` is the set of functions `f : ℕ → α` with `f i ∈ S i` for `i < n` and `f i = 0` for `i ≥ n`.
The proof of the uncrossing step sums over such functions. `viewL` reads such a function from one number. The
program of the pseudocode layer sums over that number.
-/

namespace UncrossingWires

open Finset

section Cube

variable {α : Type*} [Zero α]

/-- The extension by zero of a function on `Fin n`. -/
def extF {n : ℕ} (g : Fin n → α) : ℕ → α := fun i => if h : i < n then g ⟨i, h⟩ else 0

theorem extF_injective (n : ℕ) : Function.Injective (extF (α := α) (n := n)) := by
  intro g g' h
  funext i
  have := congrFun h i
  simpa [extF, i.2] using this

/-- The functions on `ℕ` that vanish from `n` on, and with values in `S i` below `n`. -/
noncomputable def cube (n : ℕ) (S : ℕ → Finset α) : Finset (ℕ → α) :=
  (Fintype.piFinset fun i : Fin n => S i).map ⟨extF, extF_injective n⟩

theorem mem_cube {n : ℕ} {S : ℕ → Finset α} {f : ℕ → α} :
    f ∈ cube n S ↔ (∀ i < n, f i ∈ S i) ∧ ∀ i, n ≤ i → f i = 0 := by
  constructor
  · intro h
    rw [cube, Finset.mem_map] at h
    obtain ⟨g, hg, rfl⟩ := h
    rw [Fintype.mem_piFinset] at hg
    constructor
    · intro i hi
      simpa [extF, hi] using hg ⟨i, hi⟩
    · intro i hi
      simp [extF, Nat.not_lt.mpr hi]
  · rintro ⟨h1, h2⟩
    rw [cube, Finset.mem_map]
    refine ⟨fun i => f i, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      exact h1 i i.2
    · funext i
      by_cases hi : i < n
      · simp [extF, hi]
      · simp [extF, hi, h2 i (Nat.not_lt.mp hi)]

/-- A sum over a cube of a product is a product of sums. -/
theorem sum_cube_prod {β : Type*} [CommRing β] (n : ℕ) (S : ℕ → Finset α) (g : ℕ → α → β) :
    ∑ f ∈ cube n S, ∏ i ∈ range n, g i (f i) = ∏ i ∈ range n, ∑ x ∈ S i, g i x := by
  rw [Finset.prod_range (fun i => ∑ x ∈ S i, g i x), Finset.prod_univ_sum, cube, Finset.sum_map]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [extF]

/-- Adding the top index. -/
theorem sum_cube_succ {β : Type*} [AddCommMonoid β] (n : ℕ) (S : ℕ → Finset α) (G : (ℕ → α) → β) :
    ∑ f ∈ cube (n + 1) S, G f = ∑ f ∈ cube n S, ∑ x ∈ S n, G (Function.update f n x) := by
  rw [← Finset.sum_product' (f := fun f x => G (Function.update f n x))]
  refine Finset.sum_nbij' (fun f => (Function.update f n 0, f n))
    (fun p => Function.update p.1 n p.2) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_cube] at hf
    rw [Finset.mem_product, mem_cube]
    refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, hf.1 n (Nat.lt_succ_self n)⟩
    · change Function.update f n 0 i ∈ S i
      rw [Function.update_of_ne hi.ne]
      exact hf.1 i (Nat.lt_succ_of_lt hi)
    · change Function.update f n 0 i = 0
      rcases Nat.eq_or_lt_of_le hi with rfl | h
      · simp
      · rw [Function.update_of_ne h.ne']
        exact hf.2 i h
  · rintro ⟨f, x⟩ hp
    rw [Finset.mem_product, mem_cube] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    rw [mem_cube]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · rw [Function.update_of_ne h.ne]
        exact h1 i h
      · simpa using h3
    · rw [Function.update_of_ne (by omega)]
      exact h2 i (by omega)
  · intro f _
    simp
  · rintro ⟨f, x⟩ hp
    rw [Finset.mem_product, mem_cube] at hp
    obtain ⟨⟨_, h2⟩, _⟩ := hp
    have hfn : f n = 0 := h2 n le_rfl
    simp [hfn]
  · intro f _
    simp

/-- A bijection on each coordinate gives a bijection of cubes. -/
theorem sum_cube_map {α' : Type*} [Zero α'] {β : Type*} [AddCommMonoid β] (n : ℕ) (S : ℕ → Finset α)
    (S' : ℕ → Finset α') (φ : ℕ → α → α')
    (hφ : ∀ i, Set.BijOn (φ i) (S i) (S' i)) (h0 : ∀ i, φ i 0 = 0) (G : (ℕ → α') → β) :
    ∑ f ∈ cube n S, G (fun i => φ i (f i)) = ∑ f ∈ cube n S', G f := by
  refine Finset.sum_bij (fun f _ => fun i => φ i (f i)) ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_cube] at hf ⊢
    exact ⟨fun i hi => (hφ i).mapsTo (hf.1 i hi), fun i hi => by simp [hf.2 i hi, h0]⟩
  · intro f hf f' hf' h
    rw [mem_cube] at hf hf'
    funext i
    by_cases hi : i < n
    · exact (hφ i).injOn (hf.1 i hi) (hf'.1 i hi) (congrFun h i)
    · rw [hf.2 i (Nat.not_lt.mp hi), hf'.2 i (Nat.not_lt.mp hi)]
  · intro f' hf'
    rw [mem_cube] at hf'
    have hex : ∀ i < n, ∃ x, x ∈ S i ∧ φ i x = f' i := fun i hi => by
      obtain ⟨x, hx, hxe⟩ := (hφ i).surjOn (hf'.1 i hi)
      exact ⟨x, hx, hxe⟩
    choose! F hF hF' using hex
    refine ⟨fun i => if i < n then F i else 0, ?_, ?_⟩
    · rw [mem_cube]
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · simpa [hi] using hF i hi
      · simp [Nat.not_lt.mpr hi]
    · funext i
      by_cases hi : i < n
      · simpa [hi] using hF' i hi
      · simp [hi, h0, hf'.2 i (Nat.not_lt.mp hi)]
  · intro f _
    rfl

end Cube

/-! ### Reading a function from one number -/

/-- Field `i` of the number `Z`, where field `t` has width `a t`. The value is zero from `n` on. -/
def viewL (n : ℕ) (a : ℕ → ℕ) (Z i : ℕ) : ℕ :=
  if i < n then Z / 2 ^ (∑ t ∈ range i, a t) % 2 ^ a i else 0

private theorem viewL_low (a : ℕ → ℕ) {n i : ℕ} (hi : i < n) (x y : ℕ) :
    (x + 2 ^ (∑ t ∈ range n, a t) * y) / 2 ^ (∑ t ∈ range i, a t) % 2 ^ a i =
      x / 2 ^ (∑ t ∈ range i, a t) % 2 ^ a i := by
  have hle : ∑ t ∈ range (i + 1), a t ≤ ∑ t ∈ range n, a t :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hi)
  rw [Finset.sum_range_succ] at hle
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
  rw [he, pow_add, pow_add, mul_assoc, mul_assoc,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

private theorem viewL_succ (n : ℕ) (a : ℕ → ℕ) {x y : ℕ} (hx : x < 2 ^ ∑ t ∈ range n, a t)
    (hy : y < 2 ^ a n) :
    viewL (n + 1) a (x + 2 ^ (∑ t ∈ range n, a t) * y) = Function.update (viewL n a x) n y := by
  funext i
  rcases lt_trichotomy i n with h | rfl | h
  · rw [Function.update_of_ne h.ne]
    simp only [viewL, h, Nat.lt_succ_of_lt h, if_true]
    exact viewL_low a h x y
  · simp only [viewL, Nat.lt_succ_self, if_true, Function.update_self]
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add,
      Nat.mod_eq_of_lt hy]
  · rw [Function.update_of_ne h.ne']
    simp only [viewL, Nat.not_lt.mpr h.le, Nat.not_lt.mpr (Nat.succ_le_of_lt h), if_false]

private theorem viewL_mapsTo (n : ℕ) (a : ℕ → ℕ) (Z : ℕ) :
    viewL n a Z ∈ cube n (fun i => range (2 ^ a i)) := by
  rw [mem_cube]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · simp only [viewL, hi, if_true, Finset.mem_range]
    exact Nat.mod_lt _ (by positivity)
  · simp [viewL, Nat.not_lt.mpr hi]

private theorem viewL_bijOn_aux (n : ℕ) (a : ℕ → ℕ) :
    Set.BijOn (viewL n a) (range (2 ^ ∑ t ∈ range n, a t) : Finset ℕ)
      (cube n (fun i => range (2 ^ a i)) : Finset (ℕ → ℕ)) := by
  induction n with
  | zero =>
    refine ⟨fun Z _ => viewL_mapsTo 0 a Z, ?_, ?_⟩
    · intro Z hZ Z' hZ' _
      simp only [Finset.sum_range_zero, pow_zero, Finset.coe_range, Set.mem_Iio] at hZ hZ'
      omega
    · intro f hf
      rw [Finset.mem_coe, mem_cube] at hf
      refine ⟨0, by simp, ?_⟩
      funext i
      simp [viewL, hf.2 i (Nat.zero_le i)]
  | succ n ih =>
    have hA : (0 : ℕ) < 2 ^ ∑ t ∈ range n, a t := by positivity
    refine ⟨fun Z _ => viewL_mapsTo (n + 1) a Z, ?_, ?_⟩
    · intro Z hZ Z' hZ' h
      rw [Finset.mem_coe, Finset.mem_range, Finset.sum_range_succ, pow_add] at hZ hZ'
      have hx := Nat.mod_lt Z hA
      have hx' := Nat.mod_lt Z' hA
      have hy := Nat.div_lt_of_lt_mul hZ
      have hy' := Nat.div_lt_of_lt_mul hZ'
      have hZe := Nat.mod_add_div Z (2 ^ ∑ t ∈ range n, a t)
      have hZe' := Nat.mod_add_div Z' (2 ^ ∑ t ∈ range n, a t)
      have hu := viewL_succ n a hx hy
      have hu' := viewL_succ n a hx' hy'
      rw [hZe] at hu
      rw [hZe'] at hu'
      rw [h, hu'] at hu
      have htop : Z' / 2 ^ (∑ t ∈ range n, a t) = Z / 2 ^ (∑ t ∈ range n, a t) := by
        simpa using congrFun hu n
      have hlow : viewL n a (Z' % 2 ^ ∑ t ∈ range n, a t) = viewL n a (Z % 2 ^ ∑ t ∈ range n, a t) := by
        funext i
        by_cases hin : i = n
        · subst hin
          simp [viewL]
        · simpa [Function.update_of_ne hin] using congrFun hu i
      have hmod := ih.injOn (by simpa using hx') (by simpa using hx) hlow
      rw [← hZe, ← hZe', hmod, htop]
    · intro f hf
      rw [Finset.mem_coe, mem_cube] at hf
      have hg : Function.update f n 0 ∈ cube n (fun i => range (2 ^ a i)) := by
        rw [mem_cube]
        refine ⟨fun i hi => ?_, fun i hi => ?_⟩
        · rw [Function.update_of_ne hi.ne]
          exact hf.1 i (Nat.lt_succ_of_lt hi)
        · rcases Nat.eq_or_lt_of_le hi with rfl | h
          · simp
          · rw [Function.update_of_ne h.ne']
            exact hf.2 i h
      obtain ⟨x, hx, hxe⟩ := ih.surjOn (Finset.mem_coe.mpr hg)
      have hx' : x < 2 ^ ∑ t ∈ range n, a t := by simpa using hx
      have hy : f n < 2 ^ a n := by simpa using hf.1 n (Nat.lt_succ_self n)
      refine ⟨x + 2 ^ (∑ t ∈ range n, a t) * f n, ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_range, Finset.sum_range_succ, pow_add]
        calc x + 2 ^ (∑ t ∈ range n, a t) * f n
            < 2 ^ (∑ t ∈ range n, a t) + 2 ^ (∑ t ∈ range n, a t) * f n := by omega
          _ = 2 ^ (∑ t ∈ range n, a t) * (f n + 1) := by ring
          _ ≤ 2 ^ (∑ t ∈ range n, a t) * 2 ^ a n := Nat.mul_le_mul_left _ hy
      · rw [viewL_succ n a hx' hy, hxe]
        simp

/-- A sum over the numbers below `2 ^ (a 0 + ... + a (n - 1))` is a sum over the cube of their fields. -/
theorem sum_viewL {β : Type*} [AddCommMonoid β] (n : ℕ) (a : ℕ → ℕ) (G : (ℕ → ℕ) → β) :
    ∑ Z ∈ range (2 ^ ∑ t ∈ range n, a t), G (viewL n a Z) =
      ∑ f ∈ cube n (fun i => range (2 ^ a i)), G f := by
  have h := viewL_bijOn_aux n a
  exact Finset.sum_nbij (viewL n a) (fun Z _ => viewL_mapsTo n a Z) h.injOn h.surjOn (fun _ _ => rfl)

/-- `viewL` is a bijection onto the cube. -/
theorem viewL_bijOn (n : ℕ) (a : ℕ → ℕ) :
    Set.BijOn (viewL n a) (range (2 ^ ∑ t ∈ range n, a t) : Finset ℕ)
      (cube n (fun i => range (2 ^ a i)) : Finset (ℕ → ℕ)) :=
  viewL_bijOn_aux n a

/-- A product of sums over the fields of one number. -/
theorem prod_sum_viewL {β : Type*} [CommRing β] (n : ℕ) (a : ℕ → ℕ) (g : ℕ → ℕ → β) :
    ∑ Z ∈ range (2 ^ ∑ t ∈ range n, a t), ∏ i ∈ range n, g i (viewL n a Z i) =
      ∏ i ∈ range n, ∑ x ∈ range (2 ^ a i), g i x := by
  rw [sum_viewL n a (fun f => ∏ i ∈ range n, g i (f i)), sum_cube_prod]

/-- Two-level reading: the numbers of the words `v < n`, each with fields `a v y`, `y < k`, are read from one number. -/
theorem sum_viewL_two {β : Type*} [AddCommMonoid β] (n k : ℕ) (a : ℕ → ℕ → ℕ) (G : (ℕ → ℕ → ℕ) → β) :
    ∑ Z ∈ range (2 ^ ∑ v ∈ range n, ∑ y ∈ range k, a v y),
        G (fun v => viewL k (a v) (viewL n (fun v => ∑ y ∈ range k, a v y) Z v)) =
      ∑ B ∈ cube n (fun v => cube k (fun y => range (2 ^ a v y))), G B := by
  rw [sum_viewL n (fun v => ∑ y ∈ range k, a v y) (fun f => G (fun v => viewL k (a v) (f v)))]
  refine sum_cube_map n _ _ (fun v => viewL k (a v)) (fun v => viewL_bijOn_aux k (a v)) ?_ G
  intro v
  funext y
  simp [viewL]

private theorem sum_range_mul' {β : Type*} [AddCommMonoid β] (A B : ℕ) (G : ℕ → β) :
    ∑ Z ∈ range (A * B), G Z = ∑ y ∈ range B, ∑ x ∈ range A, G (x + A * y) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.add_comm]

/-- One number splits into its low and high parts. -/
theorem sum_split {β : Type*} [AddCommMonoid β] (a b : ℕ) (G : ℕ → β) :
    ∑ Z ∈ range (2 ^ (a + b)), G Z = ∑ y ∈ range (2 ^ b), ∑ x ∈ range (2 ^ a), G (x + 2 ^ a * y) := by
  rw [pow_add, sum_range_mul']

/-! ### Symmetric families -/

private theorem prod_pairs {β : Type*} [CommMonoid β] (n : ℕ) (F : ℕ → ℕ → β)
    (hF : ∀ u, F u u = 1) :
    ∏ u ∈ range n, ∏ u' ∈ range n, F u u' =
      ∏ u ∈ range n, ∏ u' ∈ range n, if u < u' then F u u' * F u' u else 1 := by
  have h1 : ∀ u u', F u u' = (if u < u' then F u u' else 1) * (if u' < u then F u u' else 1) := by
    intro u u'
    rcases lt_trichotomy u u' with h | rfl | h
    · simp [h, Nat.not_lt.mpr h.le]
    · simp [hF]
    · simp [h, Nat.not_lt.mpr h.le]
  have h2 : ∀ u u', (if u < u' then F u u' * F u' u else 1) =
      (if u < u' then F u u' else 1) * (if u < u' then F u' u else 1) := by
    intro u u'
    split_ifs <;> simp
  calc ∏ u ∈ range n, ∏ u' ∈ range n, F u u'
      = (∏ u ∈ range n, ∏ u' ∈ range n, if u < u' then F u u' else 1) *
          ∏ u ∈ range n, ∏ u' ∈ range n, if u' < u then F u u' else 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun u _ => ?_
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun u' _ => h1 u u'
    _ = (∏ u ∈ range n, ∏ u' ∈ range n, if u < u' then F u u' else 1) *
          ∏ u ∈ range n, ∏ u' ∈ range n, if u < u' then F u' u else 1 := by
        rw [Finset.prod_comm (f := fun u u' => if u' < u then F u u' else 1)]
    _ = ∏ u ∈ range n, ∏ u' ∈ range n, if u < u' then F u u' * F u' u else 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun u _ => ?_
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun u' _ => (h2 u u').symm

/-- A sum over the symmetric functions with zero diagonal is a product over the pairs `u < u'`. -/
theorem sum_symm_prod {β : Type*} [CommRing β] (n : ℕ) (w : ℕ → ℕ → ℕ) (hsym : ∀ x y, w x y = w y x)
    (h0 : ∀ x, w x x = 0) (g : ℕ → ℕ → ℕ → β) :
    ∑ B ∈ cube n (fun x => cube n (fun y => range (2 ^ w x y))),
        (if ∀ x < n, ∀ y < n, B x y = B y x then 1 else 0) *
          ∏ u ∈ range n, ∏ u' ∈ range n, (if u' = u then 1 else g u u' (B u u')) =
      ∏ u ∈ range n, ∏ u' ∈ range n,
        (if u < u' then ∑ b ∈ range (2 ^ w u u'), g u u' b * g u' u b else 1) := by
  classical
  set S : ℕ → ℕ → Finset ℕ := fun u u' => if u < u' then range (2 ^ w u u') else {0} with hS
  set H : ℕ → ℕ → ℕ → β := fun u u' b => if u < u' then g u u' b * g u' u b else 1 with hH
  -- the right side is a sum over a cube
  have hR : ∏ u ∈ range n, ∏ u' ∈ range n,
        (if u < u' then ∑ b ∈ range (2 ^ w u u'), g u u' b * g u' u b else 1) =
      ∑ b ∈ cube n (fun u => cube n (S u)), ∏ u ∈ range n, ∏ u' ∈ range n, H u u' (b u u') := by
    rw [sum_cube_prod n (fun u => cube n (S u)) (fun u f => ∏ u' ∈ range n, H u u' (f u'))]
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [sum_cube_prod n (S u) (H u)]
    refine Finset.prod_congr rfl fun u' _ => ?_
    by_cases huu : u < u'
    · simp [hS, hH, huu]
    · simp [hS, hH, huu]
  rw [hR]
  -- the left side is a sum over the symmetric families
  have hL : ∀ B : ℕ → ℕ → ℕ,
      ((if ∀ x < n, ∀ y < n, B x y = B y x then 1 else 0) *
          ∏ u ∈ range n, ∏ u' ∈ range n, (if u' = u then 1 else g u u' (B u u')) : β) =
        if ∀ x < n, ∀ y < n, B x y = B y x then
          ∏ u ∈ range n, ∏ u' ∈ range n, (if u' = u then 1 else g u u' (B u u')) else 0 := by
    intro B
    split_ifs <;> simp
  simp only [hL]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun B u u' => if u < u' then B u u' else 0)
    (fun b u u' => if u < u' then b u u' else if u' < u then b u' u else 0) ?_ ?_ ?_ ?_ ?_
  · -- the map to the cube of the upper triangle
    intro B hB
    rw [Finset.mem_filter, mem_cube] at hB
    obtain ⟨⟨hB1, hB2⟩, _⟩ := hB
    rw [mem_cube]
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · have hBu := hB1 u hu
      rw [mem_cube] at hBu ⊢
      refine ⟨fun u' hu' => ?_, fun u' hu' => ?_⟩
      · by_cases huu : u < u'
        · simpa [hS, huu] using hBu.1 u' hu'
        · simp [hS, huu]
      · simp [hBu.2 u' hu']
    · funext u'
      simp [hB2 u hu]
  · -- the map to the symmetric families
    intro b hb
    rw [mem_cube] at hb
    obtain ⟨hb1, hb2⟩ := hb
    rw [Finset.mem_filter, mem_cube]
    refine ⟨⟨fun u hu => ?_, fun u hu => ?_⟩, fun x _ y _ => ?_⟩
    · have hbu := hb1 u hu
      rw [mem_cube] at hbu ⊢
      refine ⟨fun u' hu' => ?_, fun u' hu' => ?_⟩
      · rcases lt_trichotomy u u' with h | rfl | h
        · have := hbu.1 u' hu'
          simpa [hS, h] using this
        · simp
        · have hbu' := hb1 u' hu'
          rw [mem_cube] at hbu'
          have := hbu'.1 u hu
          simp only [hS, h, if_true] at this
          simpa [Nat.not_lt.mpr h.le, h, hsym u u'] using this
      · have hnot : ¬ u' < u := by omega
        simp [hbu.2 u' hu', hnot]
    · funext u'
      by_cases huu : u < u'
      · simp [huu, hb2 u hu]
      · by_cases huu' : u' < u
        · have hzero : b u' u = 0 := by
            by_cases hu' : u' < n
            · have hbu' := hb1 u' hu'
              rw [mem_cube] at hbu'
              exact hbu'.2 u hu
            · rw [hb2 u' (Nat.not_lt.mp hu')]
              rfl
          simp [huu, huu', hzero]
        · simp [huu, huu']
    · rcases lt_trichotomy x y with h | rfl | h
      · simp [h, Nat.not_lt.mpr h.le]
      · rfl
      · simp [h, Nat.not_lt.mpr h.le]
  · -- the left inverse
    intro B hB
    rw [Finset.mem_filter, mem_cube] at hB
    obtain ⟨⟨hB1, hB2⟩, hB3⟩ := hB
    have hzero : ∀ x y, n ≤ x → B x y = 0 := by
      intro x y hx
      rw [hB2 x hx]
      rfl
    have hzero' : ∀ x y, n ≤ y → B x y = 0 := by
      intro x y hy
      by_cases hx : x < n
      · have := hB1 x hx
        rw [mem_cube] at this
        exact this.2 y hy
      · exact hzero x y (Nat.not_lt.mp hx)
    funext u u'
    rcases lt_trichotomy u u' with h | rfl | h
    · simp [h]
    · by_cases hu : u < n
      · have := hB1 u hu
        rw [mem_cube] at this
        have h2 := this.1 u hu
        simp only [h0, pow_zero, Finset.mem_range, Nat.lt_one_iff] at h2
        simp [h2]
      · simp [hzero u u (Nat.not_lt.mp hu)]
    · have hnot : ¬ u < u' := by omega
      by_cases hu : u < n
      · simp [hnot, h, hB3 u hu u' (by omega)]
      · simp [hnot, h, hzero u u' (Nat.not_lt.mp hu), hzero' u' u (Nat.not_lt.mp hu)]
  · -- the right inverse
    intro b hb
    rw [mem_cube] at hb
    obtain ⟨hb1, hb2⟩ := hb
    funext u u'
    by_cases huu : u < u'
    · simp [huu]
    · have hzero : b u u' = 0 := by
        by_cases hu : u < n
        · have hbu := hb1 u hu
          rw [mem_cube] at hbu
          by_cases hu' : u' < n
          · have := hbu.1 u' hu'
            simpa [hS, huu] using this
          · exact hbu.2 u' (Nat.not_lt.mp hu')
        · rw [hb2 u (Nat.not_lt.mp hu)]
          rfl
      simp [huu, hzero]
  · -- the weights
    intro B hB
    rw [Finset.mem_filter] at hB
    have hsymB := hB.2
    rw [prod_pairs n (fun u u' => if u' = u then 1 else g u u' (B u u')) (by intro u; simp)]
    refine Finset.prod_congr rfl fun u hu => Finset.prod_congr rfl fun u' hu' => ?_
    rw [Finset.mem_range] at hu hu'
    by_cases huu : u < u'
    · have h1 : u' ≠ u := by omega
      have h2 : u ≠ u' := by omega
      simp [hH, huu, h1, h2, hsymB u' hu' u hu]
    · simp [hH, huu]

end UncrossingWires
