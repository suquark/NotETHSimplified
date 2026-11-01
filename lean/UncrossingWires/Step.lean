import UncrossingWires.Seed

/-!
# One step: from `K' * K'` words to `K'` words

A *level* has `K` words, numbered below `K`. A weight `w x y` is the number of wires between the words `x` and `y`. The
wires of the pair `x, y` hold one number `B x y < 2 ^ w x y` at the word `x`, and one number `B y x` at the word `y`.
The wires hold equal bits if `B x y = B y x`. A word function `F x` reads the numbers `B x`.

`val K w F` is the sum, over the families `B` of numbers with `B x y = B y x`, of the product of `F x (B x)`.

The word `(a, b)` has the number `a * K' + b`. A direction `dir` says which coordinate the next level keeps:
`dir = true` keeps the row `a`, and `dir = false` keeps the column `b`. In the coordinates of the direction, a word is
`wd u v`, and `u` is the coordinate that the next level keeps. `step_val` is the theorem of this file.
-/

namespace UncrossingWires

open Finset

/-- The data of one step. The bits of `c` choose a piece for each rectangle. -/
structure Lev where
  K' : ℕ
  w : ℕ → ℕ → ℕ
  c : ℕ
  dir : Bool
  scale : ℕ

namespace Lev

variable (l : Lev)

/-- The word with coordinates `u`, `v`, for the direction. -/
def wd (u v : ℕ) : ℕ := if l.dir then u * l.K' + v else v * l.K' + u

/-- The paired wires on the diagonal from `wd u v` to `wd u' v'`. -/
def pm (u u' v v' : ℕ) : ℕ :=
  if u = u' ∨ v = v' then 0 else oddMin (l.w (l.wd u v) (l.wd u' v')) (l.w (l.wd u v') (l.wd u' v))

/-- The bit of the code `c` for the rectangle, in the coordinates of rows and columns. -/
def idx (u u' v v' : ℕ) : ℕ :=
  if l.dir then ((u * l.K' + u') * l.K' + v) * l.K' + v' else ((v * l.K' + v') * l.K' + u) * l.K' + u'

/-- The piece of the rectangle. -/
def pol (u u' v v' : ℕ) : Bool := !(l.c.testBit (l.idx u u' v v'))

/-- The index wires of the segment `(v, v')` of a pair `u < u'`. -/
def dd (u u' v v' : ℕ) : ℕ :=
  if v < v' then dLen (l.pol u u' v v' == l.dir) (l.pm u u' v v') else 0

/-- The wires of the segment `(v, v')` that stay wires. -/
def carry (u u' v v' : ℕ) : ℕ := l.w (l.wd u v) (l.wd u' v') - l.pm u u' v v'

/-- The new wires of the segment `(v, v')` of a pair `u < u'`. -/
def seg (u u' v v' : ℕ) : ℕ := l.carry u u' v v' + l.dd u u' v v'

/-- The segment with number `s = v * K' + v'`. -/
def segS (u u' s : ℕ) : ℕ := l.seg u u' (s / l.K') (s % l.K')

/-- The weight of the next level. -/
def newW (u u' : ℕ) : ℕ :=
  if u = u' then 0 else ∑ s ∈ range (l.K' * l.K'), l.segS (min u u') (max u u') s

/-- The factor of the segment `(v, v')` at the word `u`, towards `u'`. `b` is the number of the segment, and `B v y` is
the number of the word `wd u v` towards the word `y`. -/
def segT (u u' v v' b : ℕ) (B : ℕ → ℕ → ℕ) : ℤ :=
  if u < u' then
    (if b % 2 ^ l.carry u u' v v' = B v (l.wd u' v') / 2 ^ l.pm u u' v v' then 1 else 0) *
      (if v < v' then
        rectA l.dir (l.pol u u' v v') l.scale (l.pm u u' v v') (b / 2 ^ l.carry u u' v v')
          (B v (l.wd u' v') % 2 ^ l.pm u u' v v') (B v' (l.wd u' v) % 2 ^ l.pm u u' v v')
      else 1)
  else
    (if b % 2 ^ l.carry u' u v v' = B v' (l.wd u' v) / 2 ^ l.pm u' u v v' then 1 else 0) *
      (if v < v' then
        rectB l.dir (l.pol u' u v v') (l.pm u' u v v') (b / 2 ^ l.carry u' u v v')
          (B v (l.wd u' v') % 2 ^ l.pm u' u v v') (B v' (l.wd u' v) % 2 ^ l.pm u' u v v')
      else 1)

/-- The factor at the word `u` of the next level. `B v y` are the numbers on the words `wd u v`, and `B' u'` are the
new numbers at `u`. -/
def trans (u : ℕ) (B : ℕ → ℕ → ℕ) (B' : ℕ → ℕ) : ℤ :=
  (∏ v ∈ range l.K', ∏ v' ∈ range l.K',
    if v < v' ∧ B v (l.wd u v') ≠ B v' (l.wd u v) then 0 else 1) *
  ∏ u' ∈ range l.K', if u' = u then 1 else
    ∏ s ∈ range (l.K' * l.K'),
      l.segT u u' (s / l.K') (s % l.K')
        (viewL (l.K' * l.K') (l.segS (min u u') (max u u')) (B' u') s) B

/-- The assignments of the wires on the words of one `u`. -/
noncomputable def rowCube (u : ℕ) : Finset (ℕ → ℕ → ℕ) :=
  cube l.K' (fun v => cube (l.K' * l.K') (fun y => range (2 ^ l.w (l.wd u v) y)))

/-- The word function of the next level. -/
noncomputable def stepF (F : ℕ → (ℕ → ℕ) → ℤ) (u : ℕ) (B' : ℕ → ℕ) : ℤ :=
  ∑ B ∈ l.rowCube u, l.trans u B B' * ∏ v ∈ range l.K', F (l.wd u v) (B v)

end Lev

/-- The value of a level. -/
noncomputable def val (K : ℕ) (w : ℕ → ℕ → ℕ) (F : ℕ → (ℕ → ℕ) → ℤ) : ℤ :=
  ∑ B ∈ cube K (fun x => cube K (fun y => range (2 ^ w x y))),
    (if ∀ x < K, ∀ y < K, B x y = B y x then 1 else 0) * ∏ x ∈ range K, F x (B x)

/-- The bits of the code that choose a piece for a rectangle: `a < a'` and `b < b'`. The other bits must be zero. -/
def validCode (K' c : ℕ) : Prop :=
  ∀ a < K', ∀ a' < K', ∀ b < K', ∀ b' < K', ¬ (a < a' ∧ b < b') →
    c.testBit (((a * K' + a') * K' + b) * K' + b') = false

noncomputable instance (K' c : ℕ) : Decidable (validCode K' c) := Classical.dec _

/-- The number of rectangles. -/
def nRect (K' : ℕ) : ℕ :=
  ∑ a ∈ range K', ∑ a' ∈ range K', ∑ b ∈ range K', ∑ b' ∈ range K', if a < a' ∧ b < b' then 1 else 0

/-! ## The proof of `step_val`

Fix a level `l`. `Lev.val_step` writes the value of the next level as a sum over the old numbers `B`, with the sum over
the new numbers `Lev.R` inside. `Lev.R_eq` computes `Lev.R` without a direction: a power of two, the test `Oth` on the
high parts, and the product `rectProd` of the pieces chosen by the code. `sum_code` sums over the codes, `rectP_add` gives
the crossings, and `oth_mul_cross` says that the test and the crossings are the test `B x y = B y x`. -/

/-! ### Digits and reindexing -/

theorem digit_div {K' a b : ℕ} (hb : b < K') : (a * K' + b) / K' = a := by
  have hK : 0 < K' := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem digit_mod {K' a b : ℕ} (hb : b < K') : (a * K' + b) % K' = b :=
  Nat.mul_add_mod_of_lt hb

theorem digit_lt {K' a b : ℕ} (ha : a < K') (hb : b < K') : a * K' + b < K' * K' := by
  calc a * K' + b < a * K' + K' := by omega
    _ = (a + 1) * K' := by ring
    _ ≤ K' * K' := Nat.mul_le_mul_right _ ha

theorem digit_div_lt {K' s : ℕ} (hs : s < K' * K') : s / K' < K' :=
  Nat.div_lt_of_lt_mul hs

theorem digit_mod_lt {K' s : ℕ} (hs : s < K' * K') : s % K' < K' := by
  have hK : 0 < K' := by
    rcases Nat.eq_zero_or_pos K' with h | h
    · subst h; simp at hs
    · exact h
  exact Nat.mod_lt _ hK

theorem digit_eq (K' s : ℕ) : s / K' * K' + s % K' = s := Nat.div_add_mod' s K'

/-- A product over the numbers below `n * k` is a product over their two digits. -/
theorem prod_range_digits {β : Type*} [CommMonoid β] (n k : ℕ) (f : ℕ → β) :
    ∏ x ∈ range (n * k), f x = ∏ a ∈ range n, ∏ b ∈ range k, f (a * k + b) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul, prod_range_add, ih, prod_range_succ]

/-- A product over four coordinates below `K'`. -/
def prod4 (K' : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℤ) : ℤ :=
  ∏ a ∈ range K', ∏ a' ∈ range K', ∏ b ∈ range K', ∏ b' ∈ range K', f a a' b b'

theorem prod4_congr {K' : ℕ} {f g : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : ∀ a < K', ∀ a' < K', ∀ b < K', ∀ b' < K', f a a' b b' = g a a' b b') :
    prod4 K' f = prod4 K' g :=
  prod_congr rfl fun a ha => prod_congr rfl fun a' ha' => prod_congr rfl fun b hb =>
    prod_congr rfl fun b' hb' =>
      h a (mem_range.1 ha) a' (mem_range.1 ha') b (mem_range.1 hb) b' (mem_range.1 hb')

theorem prod4_mul (K' : ℕ) (f g : ℕ → ℕ → ℕ → ℕ → ℤ) :
    prod4 K' (fun a a' b b' => f a a' b b' * g a a' b b') = prod4 K' f * prod4 K' g := by
  simp only [prod4, prod_mul_distrib]

/-- Exchange the two pairs of coordinates. -/
theorem prod4_swap (K' : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℤ) :
    prod4 K' (fun a a' b b' => f b b' a a') = prod4 K' f := by
  unfold prod4
  calc ∏ a ∈ range K', ∏ a' ∈ range K', ∏ b ∈ range K', ∏ b' ∈ range K', f b b' a a'
      = ∏ a ∈ range K', ∏ b ∈ range K', ∏ a' ∈ range K', ∏ b' ∈ range K', f b b' a a' :=
        prod_congr rfl fun a _ => prod_comm
    _ = ∏ b ∈ range K', ∏ a ∈ range K', ∏ a' ∈ range K', ∏ b' ∈ range K', f b b' a a' := prod_comm
    _ = ∏ b ∈ range K', ∏ a ∈ range K', ∏ b' ∈ range K', ∏ a' ∈ range K', f b b' a a' :=
        prod_congr rfl fun b _ => prod_congr rfl fun a _ => prod_comm
    _ = ∏ b ∈ range K', ∏ b' ∈ range K', ∏ a ∈ range K', ∏ a' ∈ range K', f b b' a a' :=
        prod_congr rfl fun b _ => prod_comm

/-- A product of tests is one test. -/
theorem prod_test {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (∏ i ∈ s, if p i then (1 : ℤ) else 0) = if ∀ i ∈ s, p i then 1 else 0 := by
  rw [prod_ite_zero, prod_const_one]

theorem test_mul (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : ℤ) else 0) * (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- One test of equality from a sum over the low part. -/
theorem sum_two_tests {N α : ℕ} (hα : α < N) (β : ℕ) (C : ℤ) :
    ∑ x ∈ range N, (if x = α then (1 : ℤ) else 0) * (if x = β then 1 else 0) * C =
      (if α = β then 1 else 0) * C := by
  have : ∀ x ∈ range N, (if x = α then (1 : ℤ) else 0) * (if x = β then 1 else 0) * C =
      if x = α then (if x = β then 1 else 0) * C else 0 := by
    intro x _
    split_ifs <;> simp
  rw [sum_congr rfl this, sum_ite_eq', if_pos (mem_range.2 hα)]

/-- The fixed power of two. -/
theorem prod_scale (K' scale : ℕ) :
    prod4 K' (fun u u' v v' => if u < u' ∧ v < v' then (2 : ℤ) ^ scale else 1) =
      2 ^ (scale * nRect K') := by
  have h : ∀ u u' v v' : ℕ, (if u < u' ∧ v < v' then (2 : ℤ) ^ scale else 1) =
      (2 ^ scale) ^ (if u < u' ∧ v < v' then 1 else 0) := by
    intro u u' v v'
    split_ifs <;> simp
  simp only [h, prod4, prod_pow_eq_pow_sum, nRect, pow_mul]

namespace Lev

variable (l : Lev)

theorem wd_true {l : Lev} (hd : l.dir = true) (u v : ℕ) : l.wd u v = u * l.K' + v := by
  simp [wd, hd]

theorem wd_false {l : Lev} (hd : l.dir = false) (u v : ℕ) : l.wd u v = v * l.K' + u := by
  simp [wd, hd]

theorem wd_lt {u v : ℕ} (hu : u < l.K') (hv : v < l.K') : l.wd u v < l.K' * l.K' := by
  unfold wd
  split_ifs
  · exact digit_lt hu hv
  · exact digit_lt hv hu

/-- The coordinate that the next level keeps. -/
def cu (x : ℕ) : ℕ := if l.dir then x / l.K' else x % l.K'

/-- The other coordinate. -/
def cv (x : ℕ) : ℕ := if l.dir then x % l.K' else x / l.K'

theorem cu_lt {x : ℕ} (hx : x < l.K' * l.K') : l.cu x < l.K' := by
  unfold cu
  split_ifs
  · exact digit_div_lt hx
  · exact digit_mod_lt hx

theorem cv_lt {x : ℕ} (hx : x < l.K' * l.K') : l.cv x < l.K' := by
  unfold cv
  split_ifs
  · exact digit_mod_lt hx
  · exact digit_div_lt hx

theorem wd_cu_cv (x : ℕ) : l.wd (l.cu x) (l.cv x) = x := by
  unfold wd cu cv
  split_ifs <;> exact digit_eq _ _

theorem cu_wd {u v : ℕ} (hu : u < l.K') (hv : v < l.K') : l.cu (l.wd u v) = u := by
  unfold wd cu
  split_ifs
  · exact digit_div hv
  · exact digit_mod hu

theorem cv_wd {u v : ℕ} (hu : u < l.K') (hv : v < l.K') : l.cv (l.wd u v) = v := by
  unfold wd cv
  split_ifs
  · exact digit_mod hv
  · exact digit_div hu

/-- A product over the words is a product over the two coordinates of the direction. -/
theorem prod_wd {β : Type*} [CommMonoid β] (f : ℕ → β) :
    ∏ x ∈ range (l.K' * l.K'), f x = ∏ u ∈ range l.K', ∏ v ∈ range l.K', f (l.wd u v) := by
  rw [prod_range_digits]
  unfold wd
  cases l.dir
  · simp only [Bool.false_eq_true, if_false]
    exact prod_comm
  · simp only [if_true]

/-- The rows of a function on words. -/
def toRows {α : Type*} [Zero α] (B : ℕ → α) : ℕ → ℕ → α :=
  fun u => if u < l.K' then fun v => if v < l.K' then B (l.wd u v) else 0 else 0

/-- The function on words of its rows. -/
def ofRows {α : Type*} [Zero α] (A : ℕ → ℕ → α) : ℕ → α :=
  fun x => if x < l.K' * l.K' then A (l.cu x) (l.cv x) else 0

theorem toRows_ofRows {α : Type*} [Zero α] {T : ℕ → Finset α} {A : ℕ → ℕ → α}
    (hA : A ∈ cube l.K' (fun u => cube l.K' (fun v => T (l.wd u v)))) :
    l.toRows (l.ofRows A) = A := by
  rw [mem_cube] at hA
  funext u v
  by_cases hu : u < l.K'
  · have h1 := hA.1 _ hu
    rw [mem_cube] at h1
    by_cases hv : v < l.K'
    · simp [toRows, ofRows, hu, hv, l.wd_lt hu hv, l.cu_wd hu hv, l.cv_wd hu hv]
    · simp [toRows, hu, hv, h1.2 v (not_lt.1 hv)]
  · have h1 := hA.2 u (not_lt.1 hu)
    simp [toRows, hu, h1]

/-- A sum over the rows of the words is a sum over the words. -/
theorem sum_cube_rows {α β : Type*} [Zero α] [AddCommMonoid β] (T : ℕ → Finset α)
    (H : (ℕ → ℕ → α) → β) :
    ∑ A ∈ cube l.K' (fun u => cube l.K' (fun v => T (l.wd u v))), H A =
      ∑ B ∈ cube (l.K' * l.K') T, H (l.toRows B) := by
  refine sum_nbij' l.ofRows l.toRows ?_ ?_ (fun A hA => l.toRows_ofRows hA) ?_ ?_
  · intro A hA
    rw [mem_cube] at hA ⊢
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have h1 := hA.1 _ (l.cu_lt hx)
      rw [mem_cube] at h1
      have h2 := h1.1 _ (l.cv_lt hx)
      rw [wd_cu_cv] at h2
      simpa [ofRows, hx] using h2
    · simp [ofRows, not_lt.2 hx]
  · intro B hB
    rw [mem_cube] at hB ⊢
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [mem_cube]
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · simpa [toRows, hu, hv] using hB.1 _ (l.wd_lt hu hv)
      · simp [toRows, hu, not_lt.2 hv]
    · funext v
      simp [toRows, not_lt.2 hu]
  · intro B hB
    rw [mem_cube] at hB
    funext x
    by_cases hx : x < l.K' * l.K'
    · simp [toRows, ofRows, hx, l.cu_lt hx, l.cv_lt hx, wd_cu_cv]
    · simp [ofRows, hx, hB.2 x (not_lt.1 hx)]
  · intro A hA
    rw [l.toRows_ofRows hA]

/-! ### The sum over the rows -/

theorem segT_congr {u u' v v' b : ℕ} {B B₂ : ℕ → ℕ → ℕ} (h : B v = B₂ v) (h' : B v' = B₂ v') :
    l.segT u u' v v' b B = l.segT u u' v v' b B₂ := by
  simp only [segT, h, h']

theorem trans_congr {u : ℕ} {B B₂ : ℕ → ℕ → ℕ} (h : ∀ v < l.K', B v = B₂ v) (B' : ℕ → ℕ) :
    l.trans u B B' = l.trans u B₂ B' := by
  unfold trans
  congr 1
  · refine prod_congr rfl fun v hv => prod_congr rfl fun v' hv' => ?_
    rw [h v (mem_range.1 hv), h v' (mem_range.1 hv')]
  · refine prod_congr rfl fun u' _ => ?_
    split_ifs
    · rfl
    · refine prod_congr rfl fun s hs => ?_
      have hs' := mem_range.1 hs
      exact l.segT_congr (h _ (digit_div_lt hs')) (h _ (digit_mod_lt hs'))

/-- The sum over the new numbers, for the old numbers `B`. -/
noncomputable def R (B : ℕ → ℕ → ℕ) : ℤ :=
  ∑ B' ∈ cube l.K' (fun x => cube l.K' (fun y => range (2 ^ l.newW x y))),
    (if ∀ x < l.K', ∀ y < l.K', B' x y = B' y x then 1 else 0) *
      ∏ u ∈ range l.K', l.trans u (fun v => B (l.wd u v)) (B' u)

/-- The product of the word functions of the next level is a sum over the old numbers. -/
theorem prod_stepF (F : ℕ → (ℕ → ℕ) → ℤ) (B' : ℕ → ℕ → ℕ) :
    ∏ u ∈ range l.K', l.stepF F u (B' u) =
      ∑ B ∈ cube (l.K' * l.K') (fun x => cube (l.K' * l.K') (fun y => range (2 ^ l.w x y))),
        (∏ x ∈ range (l.K' * l.K'), F x (B x)) *
          ∏ u ∈ range l.K', l.trans u (fun v => B (l.wd u v)) (B' u) := by
  unfold stepF
  rw [← sum_cube_prod l.K' l.rowCube
    (fun u A => l.trans u A (B' u) * ∏ v ∈ range l.K', F (l.wd u v) (A v))]
  unfold rowCube
  rw [l.sum_cube_rows (fun x => cube (l.K' * l.K') (fun y => range (2 ^ l.w x y)))
    (fun A => ∏ u ∈ range l.K', (l.trans u (A u) (B' u) *
      ∏ v ∈ range l.K', F (l.wd u v) (A u v)))]
  refine sum_congr rfl fun B _ => ?_
  rw [l.prod_wd (fun x => F x (B x)), mul_comm, ← prod_mul_distrib]
  refine prod_congr rfl fun u hu => ?_
  have hu' := mem_range.1 hu
  have h1 : l.trans u (l.toRows B u) (B' u) = l.trans u (fun v => B (l.wd u v)) (B' u) := by
    refine l.trans_congr (fun v hv => ?_) _
    simp [toRows, hu', hv]
  have h2 : ∏ v ∈ range l.K', F (l.wd u v) (l.toRows B u v) =
      ∏ v ∈ range l.K', F (l.wd u v) (B (l.wd u v)) := by
    refine prod_congr rfl fun v hv => ?_
    simp [toRows, hu', mem_range.1 hv]
  rw [h1, h2]

/-- The value of the next level, as a sum over the old numbers. -/
theorem val_step (F : ℕ → (ℕ → ℕ) → ℤ) :
    val l.K' l.newW (l.stepF F) =
      ∑ B ∈ cube (l.K' * l.K') (fun x => cube (l.K' * l.K') (fun y => range (2 ^ l.w x y))),
        (∏ x ∈ range (l.K' * l.K'), F x (B x)) * l.R B := by
  unfold val R
  simp only [prod_stepF, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun B _ => sum_congr rfl fun B' _ => ?_
  ring

/-! ### The sum over the new numbers -/

theorem newW_comm (u u' : ℕ) : l.newW u u' = l.newW u' u := by
  unfold newW
  by_cases h : u = u'
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), min_comm, max_comm]

theorem newW_self (u : ℕ) : l.newW u u = 0 := if_pos rfl

theorem newW_of_lt {u u' : ℕ} (h : u < u') :
    l.newW u u' = ∑ s ∈ range (l.K' * l.K'), l.segS u u' s := by
  unfold newW
  rw [if_neg h.ne, min_eq_left h.le, max_eq_right h.le]

/-- The factor of the pair `u, u'` at the word `u`, read from one number. -/
def pairT (B : ℕ → ℕ → ℕ) (u u' b : ℕ) : ℤ :=
  ∏ s ∈ range (l.K' * l.K'),
    l.segT u u' (s / l.K') (s % l.K')
      (viewL (l.K' * l.K') (l.segS (min u u') (max u u')) b s) (fun v => B (l.wd u v))

/-- The sum over the number of a pair is a product over the segments. -/
theorem sum_pairT (B : ℕ → ℕ → ℕ) {u u' : ℕ} (h : u < u') :
    ∑ b ∈ range (2 ^ l.newW u u'), l.pairT B u u' b * l.pairT B u' u b =
      ∏ v ∈ range l.K', ∏ v' ∈ range l.K', ∑ x ∈ range (2 ^ l.seg u u' v v'),
        l.segT u u' v v' x (fun v => B (l.wd u v)) * l.segT u' u v v' x (fun v => B (l.wd u' v)) := by
  rw [l.newW_of_lt h]
  simp only [pairT, min_eq_left h.le, max_eq_right h.le, min_eq_right h.le, max_eq_left h.le,
    ← prod_mul_distrib]
  rw [prod_sum_viewL (l.K' * l.K') (l.segS u u')
    (fun s x => l.segT u u' (s / l.K') (s % l.K') x (fun v => B (l.wd u v)) *
      l.segT u' u (s / l.K') (s % l.K') x (fun v => B (l.wd u' v)))]
  rw [prod_range_digits]
  refine prod_congr rfl fun v _ => prod_congr rfl fun v' hv' => ?_
  have hv'' := mem_range.1 hv'
  simp only [segS, digit_div hv'', digit_mod hv'']

/-- The sum over the new numbers: the tests inside a row, and the segments of the pairs. -/
theorem R_expand (B : ℕ → ℕ → ℕ) :
    l.R B =
      (∏ u ∈ range l.K', ∏ v ∈ range l.K', ∏ v' ∈ range l.K',
        if v < v' ∧ B (l.wd u v) (l.wd u v') ≠ B (l.wd u v') (l.wd u v) then (0 : ℤ) else 1) *
      ∏ u ∈ range l.K', ∏ u' ∈ range l.K', if u < u' then
        ∏ v ∈ range l.K', ∏ v' ∈ range l.K', ∑ x ∈ range (2 ^ l.seg u u' v v'),
          l.segT u u' v v' x (fun v => B (l.wd u v)) * l.segT u' u v v' x (fun v => B (l.wd u' v))
      else 1 := by
  have h := sum_symm_prod l.K' l.newW l.newW_comm l.newW_self (l.pairT B)
  have h2 : ∀ B' : ℕ → ℕ → ℕ, ∏ u ∈ range l.K', l.trans u (fun v => B (l.wd u v)) (B' u) =
      (∏ u ∈ range l.K', ∏ v ∈ range l.K', ∏ v' ∈ range l.K',
        if v < v' ∧ B (l.wd u v) (l.wd u v') ≠ B (l.wd u v') (l.wd u v) then (0 : ℤ) else 1) *
      ∏ u ∈ range l.K', ∏ u' ∈ range l.K', (if u' = u then 1 else l.pairT B u u' (B' u u')) := by
    intro B'
    rw [← prod_mul_distrib]
    rfl
  unfold R
  simp only [h2]
  simp only [mul_left_comm _ (∏ u ∈ range l.K', ∏ v ∈ range l.K', ∏ v' ∈ range l.K',
    if v < v' ∧ B (l.wd u v) (l.wd u v') ≠ B (l.wd u v') (l.wd u v) then (0 : ℤ) else 1) _]
  rw [← mul_sum, h]
  congr 1
  refine prod_congr rfl fun u _ => prod_congr rfl fun u' _ => ?_
  split_ifs with huu
  · exact l.sum_pairT B huu
  · rfl

/-! ### One segment -/

theorem pm_le_left {l : Lev} (u u' v v' : ℕ) : l.pm u u' v v' ≤ l.w (l.wd u v) (l.wd u' v') := by
  unfold pm
  split_ifs
  · exact Nat.zero_le _
  · exact oddMin_le_left _ _

/-- The high part of a number is below the width of the wires that stay wires. -/
theorem high_lt {l : Lev} {u u' v v' A : ℕ} (hA : A < 2 ^ l.w (l.wd u v) (l.wd u' v')) :
    A / 2 ^ l.pm u u' v v' < 2 ^ l.carry u u' v v' := by
  unfold carry
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
    Nat.sub_add_cancel (pm_le_left u u' v v')]
  exact hA

/-- The sum over the new number of one segment. -/
theorem seg_sum
    (hscale : ∀ x < l.K' * l.K', ∀ y < l.K' * l.K', l.w x y ≤ l.scale) (B : ℕ → ℕ → ℕ)
    (hB : ∀ x < l.K' * l.K', ∀ y < l.K' * l.K', B x y < 2 ^ l.w x y)
    {u u' v v' : ℕ} (hu : u < l.K') (hu' : u' < l.K') (hv : v < l.K') (hv' : v' < l.K')
    (huu : u < u') :
    ∑ x ∈ range (2 ^ l.seg u u' v v'),
        l.segT u u' v v' x (fun v => B (l.wd u v)) * l.segT u' u v v' x (fun v => B (l.wd u' v)) =
      (if B (l.wd u v) (l.wd u' v') / 2 ^ l.pm u u' v v' =
          B (l.wd u' v') (l.wd u v) / 2 ^ l.pm u u' v v' then 1 else 0) *
        (if v < v' then
          2 ^ l.scale * PP l.dir (l.pol u u' v v') (l.pm u u' v v')
            (B (l.wd u v) (l.wd u' v') % 2 ^ l.pm u u' v v')
            (B (l.wd u v') (l.wd u' v) % 2 ^ l.pm u u' v v')
            (B (l.wd u' v) (l.wd u v') % 2 ^ l.pm u u' v v')
            (B (l.wd u' v') (l.wd u v) % 2 ^ l.pm u u' v v')
        else 1) := by
  have hα : B (l.wd u v) (l.wd u' v') / 2 ^ l.pm u u' v v' < 2 ^ l.carry u u' v v' :=
    high_lt (hB _ (l.wd_lt hu hv) _ (l.wd_lt hu' hv'))
  have hm : l.pm u u' v v' ≤ l.scale :=
    (pm_le_left u u' v v').trans (hscale _ (l.wd_lt hu hv) _ (l.wd_lt hu' hv'))
  have hnot : ¬ u' < u := not_lt.2 huu.le
  -- The two factors of one segment, for the low and the high part of the number.
  have hT : ∀ y, ∀ x ∈ range (2 ^ l.carry u u' v v'),
      l.segT u u' v v' (x + 2 ^ l.carry u u' v v' * y) (fun v => B (l.wd u v)) *
        l.segT u' u v v' (x + 2 ^ l.carry u u' v v' * y) (fun v => B (l.wd u' v)) =
      (if x = B (l.wd u v) (l.wd u' v') / 2 ^ l.pm u u' v v' then (1 : ℤ) else 0) *
        (if x = B (l.wd u' v') (l.wd u v) / 2 ^ l.pm u u' v v' then 1 else 0) *
        ((if v < v' then
            rectA l.dir (l.pol u u' v v') l.scale (l.pm u u' v v') y
              (B (l.wd u v) (l.wd u' v') % 2 ^ l.pm u u' v v')
              (B (l.wd u v') (l.wd u' v) % 2 ^ l.pm u u' v v') else 1) *
          (if v < v' then
            rectB l.dir (l.pol u u' v v') (l.pm u u' v v') y
              (B (l.wd u' v) (l.wd u v') % 2 ^ l.pm u u' v v')
              (B (l.wd u' v') (l.wd u v) % 2 ^ l.pm u u' v v') else 1)) := by
    intro y x hx
    have hx' := mem_range.1 hx
    have hpos : 0 < 2 ^ l.carry u u' v v' := by positivity
    have e1 : (x + 2 ^ l.carry u u' v v' * y) % 2 ^ l.carry u u' v v' = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
    have e2 : (x + 2 ^ l.carry u u' v v' * y) / 2 ^ l.carry u u' v v' = y := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hx', Nat.zero_add]
    simp only [segT, if_pos huu, if_neg hnot, e1, e2]
    ring
  unfold seg
  rw [sum_split]
  have hS : ∀ y ∈ range (2 ^ l.dd u u' v v'),
      ∑ x ∈ range (2 ^ l.carry u u' v v'),
        l.segT u u' v v' (x + 2 ^ l.carry u u' v v' * y) (fun v => B (l.wd u v)) *
          l.segT u' u v v' (x + 2 ^ l.carry u u' v v' * y) (fun v => B (l.wd u' v)) =
      (if B (l.wd u v) (l.wd u' v') / 2 ^ l.pm u u' v v' =
          B (l.wd u' v') (l.wd u v) / 2 ^ l.pm u u' v v' then 1 else 0) *
        ((if v < v' then
            rectA l.dir (l.pol u u' v v') l.scale (l.pm u u' v v') y
              (B (l.wd u v) (l.wd u' v') % 2 ^ l.pm u u' v v')
              (B (l.wd u v') (l.wd u' v) % 2 ^ l.pm u u' v v') else 1) *
          (if v < v' then
            rectB l.dir (l.pol u u' v v') (l.pm u u' v v') y
              (B (l.wd u' v) (l.wd u v') % 2 ^ l.pm u u' v v')
              (B (l.wd u' v') (l.wd u v) % 2 ^ l.pm u u' v v') else 1)) := by
    intro y _
    rw [sum_congr rfl (hT y), sum_two_tests hα]
  rw [sum_congr rfl hS, ← mul_sum]
  congr 1
  by_cases hvv : v < v'
  · simp only [if_pos hvv]
    have hdd : l.dd u u' v v' = dLen (l.pol u u' v v' == l.dir) (l.pm u u' v v') := by
      simp only [dd, if_pos hvv]
    rw [hdd]
    exact seed_sum l.dir (l.pol u u' v v') hm _ _ _ _
  · simp only [if_neg hvv]
    have hdd : l.dd u u' v v' = 0 := by simp only [dd, if_neg hvv]
    rw [hdd]
    simp

end Lev

/-! ### The coordinates of rows and columns -/

/-- The paired wires of the pair of words `x`, `y`. It does not depend on a direction. -/
def pmw (K' : ℕ) (w : ℕ → ℕ → ℕ) (x y : ℕ) : ℕ :=
  if x / K' = y / K' ∨ x % K' = y % K' then 0
  else oddMin (w x y) (w (x / K' * K' + y % K') (y / K' * K' + x % K'))

theorem pmw_comm {K' : ℕ} {w : ℕ → ℕ → ℕ} (hsym : ∀ x y, w x y = w y x) (x y : ℕ) :
    pmw K' w x y = pmw K' w y x := by
  unfold pmw
  by_cases h : x / K' = y / K' ∨ x % K' = y % K'
  · rw [if_pos h, if_pos (h.imp Eq.symm Eq.symm)]
  · have h' : ¬ (y / K' = x / K' ∨ y % K' = x % K') := fun h2 => h (h2.imp Eq.symm Eq.symm)
    rw [if_neg h, if_neg h', hsym x y, hsym (x / K' * K' + y % K')]

/-- The high parts of the numbers of each pair of words agree. -/
def Oth (K' : ℕ) (w : ℕ → ℕ → ℕ) (B : ℕ → ℕ → ℕ) : Prop :=
  ∀ x < K' * K', ∀ y < K' * K', B x y / 2 ^ pmw K' w x y = B y x / 2 ^ pmw K' w x y

/-- The paired wires of the rectangle with rows `a, a'` and columns `b, b'`. -/
def mRC (K' : ℕ) (w : ℕ → ℕ → ℕ) (a a' b b' : ℕ) : ℕ :=
  oddMin (w (a * K' + b) (a' * K' + b')) (w (a * K' + b') (a' * K' + b))

/-- The piece of a rectangle. -/
def rectP (K' : ℕ) (w : ℕ → ℕ → ℕ) (B : ℕ → ℕ → ℕ) (a a' b b' : ℕ) (pol : Bool) : ℤ :=
  Ppol pol (mRC K' w a a' b b')
    (B (a * K' + b) (a' * K' + b') % 2 ^ mRC K' w a a' b b')
    (B (a * K' + b') (a' * K' + b) % 2 ^ mRC K' w a a' b b')
    (B (a' * K' + b) (a * K' + b') % 2 ^ mRC K' w a a' b b')
    (B (a' * K' + b') (a * K' + b) % 2 ^ mRC K' w a a' b b')

/-- The crossing of a rectangle. -/
def rectX (K' : ℕ) (w : ℕ → ℕ → ℕ) (B : ℕ → ℕ → ℕ) (a a' b b' : ℕ) : ℤ :=
  cross
    (B (a * K' + b) (a' * K' + b') % 2 ^ mRC K' w a a' b b')
    (B (a * K' + b') (a' * K' + b) % 2 ^ mRC K' w a a' b b')
    (B (a' * K' + b) (a * K' + b') % 2 ^ mRC K' w a a' b b')
    (B (a' * K' + b') (a * K' + b) % 2 ^ mRC K' w a a' b b')

theorem rectP_add (K' : ℕ) (w : ℕ → ℕ → ℕ) (B : ℕ → ℕ → ℕ) (a a' b b' : ℕ) :
    rectP K' w B a a' b b' true + rectP K' w B a a' b b' false = rectX K' w B a a' b b' :=
  Ppol_add (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
    (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))

/-- The bit of a rectangle in a code. -/
def idxRC (K' a a' b b' : ℕ) : ℕ := ((a * K' + a') * K' + b) * K' + b'

/-- The product of the pieces chosen by a code. -/
def rectProd (K' : ℕ) (w : ℕ → ℕ → ℕ) (c : ℕ) (B : ℕ → ℕ → ℕ) : ℤ :=
  prod4 K' fun a a' b b' =>
    if a < a' ∧ b < b' then rectP K' w B a a' b b' (!(c.testBit (idxRC K' a a' b b'))) else 1

namespace Lev

variable (l : Lev)

/-- `pm` in the coordinates of a direction is `pmw` on the two words. -/
theorem pm_eq_pmw (hsym : ∀ x y, l.w x y = l.w y x) {u u' v v' : ℕ} (hu : u < l.K') (hu' : u' < l.K')
    (hv : v < l.K') (hv' : v' < l.K') :
    l.pm u u' v v' = pmw l.K' l.w (l.wd u v) (l.wd u' v') := by
  cases hd : l.dir
  · simp only [pm, pmw, wd_false hd, digit_div hu, digit_div hu', digit_mod hu, digit_mod hu']
    by_cases h : u = u' ∨ v = v'
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h2 => h h2.symm), hsym (v' * l.K' + u)]
  · simp only [pm, pmw, wd_true hd, digit_div hv, digit_div hv', digit_mod hv, digit_mod hv']

theorem pm_comm (hsym : ∀ x y, l.w x y = l.w y x) {u u' v v' : ℕ} (hu : u < l.K') (hu' : u' < l.K')
    (hv : v < l.K') (hv' : v' < l.K') :
    l.pm u' u v' v = l.pm u u' v v' := by
  rw [l.pm_eq_pmw hsym hu hu' hv hv', l.pm_eq_pmw hsym hu' hu hv' hv, pmw_comm hsym]

theorem pm_self_left (u v v' : ℕ) : l.pm u u v v' = 0 := if_pos (Or.inl rfl)

/-- The conditions that the sum over the new numbers tests are the high parts of all pairs. -/
theorem oth_iff (hsym : ∀ x y, l.w x y = l.w y x) (B : ℕ → ℕ → ℕ) :
    Oth l.K' l.w B ↔
      (∀ u < l.K', ∀ v < l.K', ∀ v' < l.K', v < v' →
        B (l.wd u v) (l.wd u v') = B (l.wd u v') (l.wd u v)) ∧
      (∀ u < l.K', ∀ u' < l.K', ∀ v < l.K', ∀ v' < l.K', u < u' →
        B (l.wd u v) (l.wd u' v') / 2 ^ l.pm u u' v v' =
          B (l.wd u' v') (l.wd u v) / 2 ^ l.pm u u' v v') := by
  constructor
  · intro h
    constructor
    · intro u hu v hv v' hv' _
      have := h _ (l.wd_lt hu hv) _ (l.wd_lt hu hv')
      rw [← l.pm_eq_pmw hsym hu hu hv hv', l.pm_self_left] at this
      simpa using this
    · intro u hu u' hu' v hv v' hv' _
      have := h _ (l.wd_lt hu hv) _ (l.wd_lt hu' hv')
      rwa [← l.pm_eq_pmw hsym hu hu' hv hv'] at this
  · rintro ⟨h1, h2⟩ x hx y hy
    have hcu := l.cu_lt hx
    have hcv := l.cv_lt hx
    have hcu' := l.cu_lt hy
    have hcv' := l.cv_lt hy
    have ex := l.wd_cu_cv x
    have ey := l.wd_cu_cv y
    generalize l.cu x = u at hcu ex
    generalize l.cv x = v at hcv ex
    generalize l.cu y = u' at hcu' ey
    generalize l.cv y = v' at hcv' ey
    subst ex ey
    rw [← l.pm_eq_pmw hsym hcu hcu' hcv hcv']
    rcases lt_trichotomy u u' with h | h | h
    · exact h2 u hcu u' hcu' v hcv v' hcv' h
    · subst h
      rw [l.pm_self_left, pow_zero, Nat.div_one, Nat.div_one]
      rcases lt_trichotomy v v' with h | h | h
      · exact h1 u hcu v hcv v' hcv' h
      · rw [h]
      · exact (h1 u hcu v' hcv' v hcv h).symm
    · have := h2 u' hcu' u hcu v' hcv' v hcv h
      rw [l.pm_comm hsym hcu hcu' hcv hcv'] at this
      exact this.symm

/-- The tests of the sum over the new numbers are one test. -/
theorem tests_eq (hsym : ∀ x y, l.w x y = l.w y x) (B : ℕ → ℕ → ℕ) [Decidable (Oth l.K' l.w B)] :
    (∏ u ∈ range l.K', ∏ v ∈ range l.K', ∏ v' ∈ range l.K',
        if v < v' ∧ B (l.wd u v) (l.wd u v') ≠ B (l.wd u v') (l.wd u v) then (0 : ℤ) else 1) *
      prod4 l.K' (fun u u' v v' => if u < u' then
        (if B (l.wd u v) (l.wd u' v') / 2 ^ l.pm u u' v v' =
          B (l.wd u' v') (l.wd u v) / 2 ^ l.pm u u' v v' then 1 else 0) else 1) =
      if Oth l.K' l.w B then 1 else 0 := by
  classical
  have e1 : ∀ (p : Prop) [Decidable p] (X Y : ℕ),
      (if p ∧ X ≠ Y then (0 : ℤ) else 1) = if (p → X = Y) then 1 else 0 := by
    intro p _ X Y
    by_cases hp : p <;> by_cases hX : X = Y <;> simp [hp, hX]
  have e2 : ∀ (p q : Prop) [Decidable p] [Decidable q],
      (if p then (if q then (1 : ℤ) else 0) else 1) = if (p → q) then 1 else 0 := by
    intro p q _ _
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  unfold prod4
  simp only [e1, e2, prod_test, test_mul, mem_range]
  refine if_congr ?_ rfl rfl
  rw [l.oth_iff hsym B]

/-- The piece of a rectangle of the direction, in the coordinates of rows and columns. -/
theorem PP_eq (hsym : ∀ x y, l.w x y = l.w y x) (B : ℕ → ℕ → ℕ) {u u' v v' : ℕ} (huu : u < u')
    (hvv : v < v') :
    PP l.dir (l.pol u u' v v') (l.pm u u' v v')
        (B (l.wd u v) (l.wd u' v') % 2 ^ l.pm u u' v v')
        (B (l.wd u v') (l.wd u' v) % 2 ^ l.pm u u' v v')
        (B (l.wd u' v) (l.wd u v') % 2 ^ l.pm u u' v v')
        (B (l.wd u' v') (l.wd u v) % 2 ^ l.pm u u' v v') =
      if l.dir then rectP l.K' l.w B u u' v v' (!(l.c.testBit (idxRC l.K' u u' v v')))
      else rectP l.K' l.w B v v' u u' (!(l.c.testBit (idxRC l.K' v v' u u'))) := by
  have hne : ¬ (u = u' ∨ v = v') := by
    rintro (h | h)
    · exact huu.ne h
    · exact hvv.ne h
  cases hd : l.dir
  · have hm : l.pm u u' v v' = mRC l.K' l.w v v' u u' := by
      simp only [pm, if_neg hne, wd_false hd, mRC]
      rw [hsym (v' * l.K' + u)]
    simp only [PP, hd, Bool.false_eq_true, if_false, pol, idx, hm, wd_false hd, rectP, idxRC]
  · have hm : l.pm u u' v v' = mRC l.K' l.w u u' v v' := by
      simp only [pm, if_neg hne, wd_true hd, mRC]
    simp only [PP, hd, if_true, pol, idx, hm, wd_true hd, rectP, idxRC]

/-- The product over the rectangles of the direction. -/
theorem prod_PP (hsym : ∀ x y, l.w x y = l.w y x) (B : ℕ → ℕ → ℕ) :
    prod4 l.K' (fun u u' v v' => if u < u' ∧ v < v' then
      PP l.dir (l.pol u u' v v') (l.pm u u' v v')
        (B (l.wd u v) (l.wd u' v') % 2 ^ l.pm u u' v v')
        (B (l.wd u v') (l.wd u' v) % 2 ^ l.pm u u' v v')
        (B (l.wd u' v) (l.wd u v') % 2 ^ l.pm u u' v v')
        (B (l.wd u' v') (l.wd u v) % 2 ^ l.pm u u' v v') else 1) =
      rectProd l.K' l.w l.c B := by
  have h : ∀ u u' v v' : ℕ, (if u < u' ∧ v < v' then
      PP l.dir (l.pol u u' v v') (l.pm u u' v v')
        (B (l.wd u v) (l.wd u' v') % 2 ^ l.pm u u' v v')
        (B (l.wd u v') (l.wd u' v) % 2 ^ l.pm u u' v v')
        (B (l.wd u' v) (l.wd u v') % 2 ^ l.pm u u' v v')
        (B (l.wd u' v') (l.wd u v) % 2 ^ l.pm u u' v v') else 1) =
      if u < u' ∧ v < v' then
        (if l.dir then rectP l.K' l.w B u u' v v' (!(l.c.testBit (idxRC l.K' u u' v v')))
        else rectP l.K' l.w B v v' u u' (!(l.c.testBit (idxRC l.K' v v' u u')))) else 1 := by
    intro u u' v v'
    by_cases hr : u < u' ∧ v < v'
    · rw [if_pos hr, if_pos hr]
      exact l.PP_eq hsym B hr.1 hr.2
    · rw [if_neg hr, if_neg hr]
  simp only [h]
  unfold rectProd
  cases hd : l.dir
  · simp only [Bool.false_eq_true, if_false]
    rw [← prod4_swap l.K' (fun a a' b b' => if a < a' ∧ b < b' then
      rectP l.K' l.w B a a' b b' (!(l.c.testBit (idxRC l.K' a a' b b'))) else 1)]
    refine prod4_congr fun u _ u' _ v _ v' _ => ?_
    by_cases hr : u < u' ∧ v < v'
    · rw [if_pos hr, if_pos hr.symm]
    · rw [if_neg hr, if_neg (fun h2 => hr h2.symm)]
  · simp only [if_true]

/-- **The sum over the new numbers**, without a direction. -/
theorem R_eq (hsym : ∀ x y, l.w x y = l.w y x)
    (hscale : ∀ x < l.K' * l.K', ∀ y < l.K' * l.K', l.w x y ≤ l.scale) (B : ℕ → ℕ → ℕ)
    (hB : ∀ x < l.K' * l.K', ∀ y < l.K' * l.K', B x y < 2 ^ l.w x y) [Decidable (Oth l.K' l.w B)] :
    l.R B = 2 ^ (l.scale * nRect l.K') * (if Oth l.K' l.w B then 1 else 0) *
      rectProd l.K' l.w l.c B := by
  have hpair : ∀ u ∈ range l.K', ∀ u' ∈ range l.K', (if u < u' then
        ∏ v ∈ range l.K', ∏ v' ∈ range l.K', ∑ x ∈ range (2 ^ l.seg u u' v v'),
          l.segT u u' v v' x (fun v => B (l.wd u v)) * l.segT u' u v v' x (fun v => B (l.wd u' v))
      else 1) =
      ∏ v ∈ range l.K', ∏ v' ∈ range l.K',
        ((if u < u' then
          (if B (l.wd u v) (l.wd u' v') / 2 ^ l.pm u u' v v' =
            B (l.wd u' v') (l.wd u v) / 2 ^ l.pm u u' v v' then (1 : ℤ) else 0) else 1) *
        ((if u < u' ∧ v < v' then (2 : ℤ) ^ l.scale else 1) *
          (if u < u' ∧ v < v' then
            PP l.dir (l.pol u u' v v') (l.pm u u' v v')
              (B (l.wd u v) (l.wd u' v') % 2 ^ l.pm u u' v v')
              (B (l.wd u v') (l.wd u' v) % 2 ^ l.pm u u' v v')
              (B (l.wd u' v) (l.wd u v') % 2 ^ l.pm u u' v v')
              (B (l.wd u' v') (l.wd u v) % 2 ^ l.pm u u' v v') else 1))) := by
    intro u hu u' hu'
    by_cases huu : u < u'
    · rw [if_pos huu]
      refine prod_congr rfl fun v hv => prod_congr rfl fun v' hv' => ?_
      rw [l.seg_sum hscale B hB (mem_range.1 hu) (mem_range.1 hu') (mem_range.1 hv)
        (mem_range.1 hv') huu]
      simp only [huu, true_and, if_true]
      by_cases hvv : v < v' <;> simp [hvv]
    · simp [huu]
  rw [l.R_expand B, prod_congr rfl fun u hu => prod_congr rfl fun u' hu' => hpair u hu u' hu']
  change _ * prod4 l.K' _ = _
  rw [prod4_mul, prod4_mul, l.prod_PP hsym B, prod_scale, ← mul_assoc, l.tests_eq hsym B]
  ring

end Lev

/-! ### The sum over the codes -/

/-- A sum over numbers of a product over their bits. -/
theorem sum_bits (n : ℕ) (g : ℕ → Bool → ℤ) :
    ∑ c ∈ range (2 ^ n), ∏ i ∈ range n, g i (c.testBit i) =
      ∏ i ∈ range n, (g i true + g i false) := by
  have h := prod_sum_viewL n (fun _ => 1) (fun i x => g i (decide (x = 1)))
  have hn : ∑ _t ∈ range n, 1 = n := by simp
  rw [hn] at h
  have hv : ∀ c, ∀ i ∈ range n, g i (decide (viewL n (fun _ => 1) c i = 1)) = g i (c.testBit i) := by
    intro c i hi
    have hi' := mem_range.1 hi
    have hc : ∑ _t ∈ range i, 1 = i := by simp
    simp only [viewL, if_pos hi', hc, pow_one, Nat.testBit_eq_decide_div_mod_eq]
  simp only [fun c => prod_congr rfl (hv c)] at h
  rw [h]
  refine prod_congr rfl fun i _ => ?_
  simp [Finset.sum_range_succ, add_comm]

/-- A product over the numbers below `K' ^ 4` is a product over their four digits. -/
theorem prod_range_pow_four (K' : ℕ) (Q : ℕ → ℤ) :
    ∏ i ∈ range (K' ^ 4), Q i = prod4 K' fun a a' b b' => Q (idxRC K' a a' b b') := by
  have h : K' ^ 4 = K' * K' * K' * K' := by ring
  rw [h, prod_range_digits, prod_range_digits, prod_range_digits]
  rfl

/-- The factor of one bit of a code. -/
def bitG (K' : ℕ) (P : ℕ → ℕ → ℕ → ℕ → Bool → ℤ) (i : ℕ) (bit : Bool) : ℤ :=
  if i / K' / K' / K' < i / K' / K' % K' ∧ i / K' % K' < i % K' then
    P (i / K' / K' / K') (i / K' / K' % K') (i / K' % K') (i % K') (!bit)
  else if bit then 0 else 1

theorem bitG_idx {K' : ℕ} (P : ℕ → ℕ → ℕ → ℕ → Bool → ℤ) {a a' b b' : ℕ} (ha' : a' < K')
    (hb : b < K') (hb' : b' < K') (bit : Bool) :
    bitG K' P (idxRC K' a a' b b') bit =
      if a < a' ∧ b < b' then P a a' b b' (!bit) else if bit then 0 else 1 := by
  simp only [bitG, idxRC, digit_div hb', digit_mod hb', digit_div hb, digit_mod hb,
    digit_div ha', digit_mod ha']

/-- **The sum over the codes.** Each rectangle has one bit, and the other bits are zero. -/
theorem sum_code (K' : ℕ) (P : ℕ → ℕ → ℕ → ℕ → Bool → ℤ) :
    ∑ c ∈ range (2 ^ K' ^ 4),
        (if validCode K' c then
          prod4 K' (fun a a' b b' => if a < a' ∧ b < b' then
            P a a' b b' (!(c.testBit (idxRC K' a a' b b'))) else 1)
        else 0) =
      prod4 K' (fun a a' b b' => if a < a' ∧ b < b' then
        P a a' b b' true + P a a' b b' false else 1) := by
  have hc : ∀ c, ∏ i ∈ range (K' ^ 4), bitG K' P i (c.testBit i) =
      if validCode K' c then
        prod4 K' (fun a a' b b' => if a < a' ∧ b < b' then
          P a a' b b' (!(c.testBit (idxRC K' a a' b b'))) else 1)
      else 0 := by
    intro c
    rw [prod_range_pow_four]
    have h1 : prod4 K' (fun a a' b b' => bitG K' P (idxRC K' a a' b b')
        (c.testBit (idxRC K' a a' b b'))) =
        prod4 K' (fun a a' b b' => (if a < a' ∧ b < b' then
            P a a' b b' (!(c.testBit (idxRC K' a a' b b'))) else 1) *
          (if (¬ (a < a' ∧ b < b') → c.testBit (idxRC K' a a' b b') = false) then 1 else 0)) := by
      refine prod4_congr fun a _ a' ha' b hb b' hb' => ?_
      rw [bitG_idx P ha' hb hb']
      by_cases hr : a < a' ∧ b < b'
      · simp [hr]
      · cases c.testBit (idxRC K' a a' b b') <;> simp [hr]
    have h2 : prod4 K' (fun a a' b b' =>
        (if (¬ (a < a' ∧ b < b') → c.testBit (idxRC K' a a' b b') = false) then (1 : ℤ) else 0)) =
        if validCode K' c then 1 else 0 := by
      unfold prod4
      simp only [prod_test, mem_range]
      refine if_congr ?_ rfl rfl
      simp only [mem_range]
      exact Iff.rfl
    rw [h1, prod4_mul, h2]
    split_ifs <;> simp
  simp only [← hc]
  rw [sum_bits, prod_range_pow_four]
  refine prod4_congr fun a _ a' ha' b hb b' hb' => ?_
  rw [bitG_idx P ha' hb hb', bitG_idx P ha' hb hb']
  by_cases hr : a < a' ∧ b < b'
  · simp [hr, add_comm]
  · simp [hr]

/-! ### The condition on the old numbers -/

theorem pmw_rect {K' : ℕ} {w : ℕ → ℕ → ℕ} {a a' b b' : ℕ} (hb : b < K') (hb' : b' < K')
    (ha : a ≠ a') (hbb : b ≠ b') :
    pmw K' w (a * K' + b) (a' * K' + b') = mRC K' w a a' b b' := by
  unfold pmw mRC
  simp only [digit_div hb, digit_div hb', digit_mod hb, digit_mod hb']
  rw [if_neg]
  rintro (h | h)
  · exact ha h
  · exact hbb h

/-- A number is its high part and its low part. -/
theorem eq_of_div_mod {A A' M : ℕ} (h1 : A / M = A' / M) (h2 : A % M = A' % M) : A = A' := by
  rw [← Nat.div_add_mod A M, ← Nat.div_add_mod A' M, h1, h2]

/-- The low parts of a pair in different rows and columns, with the row of `x` the smaller one. -/
theorem low_eq {K' : ℕ} {w : ℕ → ℕ → ℕ} {B : ℕ → ℕ → ℕ}
    (hX : ∀ a < K', ∀ a' < K', ∀ b < K', ∀ b' < K', a < a' ∧ b < b' →
      B (a * K' + b) (a' * K' + b') % 2 ^ mRC K' w a a' b b' =
          B (a' * K' + b') (a * K' + b) % 2 ^ mRC K' w a a' b b' ∧
        B (a * K' + b') (a' * K' + b) % 2 ^ mRC K' w a a' b b' =
          B (a' * K' + b) (a * K' + b') % 2 ^ mRC K' w a a' b b')
    {a a' b b' : ℕ} (ha : a < K') (ha' : a' < K') (hb : b < K') (hb' : b' < K') (haa : a < a') :
    B (a * K' + b) (a' * K' + b') % 2 ^ pmw K' w (a * K' + b) (a' * K' + b') =
      B (a' * K' + b') (a * K' + b) % 2 ^ pmw K' w (a * K' + b) (a' * K' + b') := by
  rcases lt_trichotomy b b' with h | h | h
  · rw [pmw_rect hb hb' haa.ne h.ne]
    exact (hX a ha a' ha' b hb b' hb' ⟨haa, h⟩).1
  · subst h
    have : pmw K' w (a * K' + b) (a' * K' + b) = 0 := by
      unfold pmw
      rw [if_pos (Or.inr (by rw [digit_mod hb, digit_mod hb]))]
    rw [this, pow_zero, Nat.mod_one, Nat.mod_one]
  · have hm : pmw K' w (a * K' + b) (a' * K' + b') = mRC K' w a a' b' b := by
      rw [pmw_rect hb hb' haa.ne h.ne']
      exact oddMin_comm _ _
    rw [hm]
    exact (hX a ha a' ha' b' hb' b hb ⟨haa, h⟩).2

/-- The numbers of all pairs agree if and only if the high parts agree and the crossings hold. -/
theorem sym_iff {K' : ℕ} {w : ℕ → ℕ → ℕ} (hsym : ∀ x y, w x y = w y x) (B : ℕ → ℕ → ℕ) :
    (∀ x < K' * K', ∀ y < K' * K', B x y = B y x) ↔
      Oth K' w B ∧ ∀ a < K', ∀ a' < K', ∀ b < K', ∀ b' < K', a < a' ∧ b < b' →
        B (a * K' + b) (a' * K' + b') % 2 ^ mRC K' w a a' b b' =
            B (a' * K' + b') (a * K' + b) % 2 ^ mRC K' w a a' b b' ∧
          B (a * K' + b') (a' * K' + b) % 2 ^ mRC K' w a a' b b' =
            B (a' * K' + b) (a * K' + b') % 2 ^ mRC K' w a a' b b' := by
  constructor
  · intro h
    refine ⟨fun x hx y hy => by rw [h x hx y hy], fun a ha a' ha' b hb b' hb' _ => ?_⟩
    rw [h _ (digit_lt ha hb) _ (digit_lt ha' hb'), h _ (digit_lt ha hb') _ (digit_lt ha' hb)]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hO, hX⟩ x hx y hy
    refine eq_of_div_mod (hO x hx y hy) ?_
    have hax := digit_div_lt hx
    have hay := digit_div_lt hy
    have hbx := digit_mod_lt hx
    have hby := digit_mod_lt hy
    have ex := digit_eq K' x
    have ey := digit_eq K' y
    generalize x / K' = a at hax ex
    generalize x % K' = b at hbx ex
    generalize y / K' = a' at hay ey
    generalize y % K' = b' at hby ey
    subst ex ey
    rcases lt_trichotomy a a' with h | h | h
    · exact low_eq hX hax hay hbx hby h
    · subst h
      have : pmw K' w (a * K' + b) (a * K' + b') = 0 := by
        unfold pmw
        rw [if_pos (Or.inl (by rw [digit_div hbx, digit_div hby]))]
      rw [this, pow_zero, Nat.mod_one, Nat.mod_one]
    · have := low_eq hX hay hax hby hbx h
      rw [pmw_comm hsym] at this
      exact this.symm

/-- The condition on the old numbers, as a product. -/
theorem oth_mul_cross {K' : ℕ} {w : ℕ → ℕ → ℕ} (hsym : ∀ x y, w x y = w y x) (B : ℕ → ℕ → ℕ)
    [Decidable (Oth K' w B)] [Decidable (∀ x < K' * K', ∀ y < K' * K', B x y = B y x)] :
    (if Oth K' w B then (1 : ℤ) else 0) *
        prod4 K' (fun a a' b b' => if a < a' ∧ b < b' then rectX K' w B a a' b b' else 1) =
      if ∀ x < K' * K', ∀ y < K' * K', B x y = B y x then 1 else 0 := by
  classical
  have e : ∀ a a' b b' : ℕ, (if a < a' ∧ b < b' then rectX K' w B a a' b b' else 1) =
      if (a < a' ∧ b < b' →
        B (a * K' + b) (a' * K' + b') % 2 ^ mRC K' w a a' b b' =
            B (a' * K' + b') (a * K' + b) % 2 ^ mRC K' w a a' b b' ∧
          B (a * K' + b') (a' * K' + b) % 2 ^ mRC K' w a a' b b' =
            B (a' * K' + b) (a * K' + b') % 2 ^ mRC K' w a a' b b') then 1 else 0 := by
    intro a a' b b'
    unfold rectX cross
    by_cases hr : a < a' ∧ b < b'
    · simp only [hr, and_self, if_true, forall_const]
    · simp [hr]
  unfold prod4
  simp only [e, prod_test, test_mul, mem_range]
  exact if_congr (sym_iff hsym B).symm rfl rfl

/-- **One step.** For any choice of the direction, the value of a level is the sum over the valid codes of the value of
the next level, up to a fixed power of two. -/
theorem step_val (K' : ℕ) (w : ℕ → ℕ → ℕ) (hsym : ∀ x y, w x y = w y x) (scale : ℕ)
    (hscale : ∀ x < K' * K', ∀ y < K' * K', w x y ≤ scale) (dirOf : ℕ → Bool) (F : ℕ → (ℕ → ℕ) → ℤ) :
    2 ^ (scale * nRect K') * val (K' * K') w F =
      ∑ c ∈ range (2 ^ K' ^ 4),
        if validCode K' c then
          val K' (Lev.newW ⟨K', w, c, dirOf c, scale⟩) (Lev.stepF ⟨K', w, c, dirOf c, scale⟩ F)
        else 0 := by
  classical
  have hval : ∀ c, val K' (Lev.newW ⟨K', w, c, dirOf c, scale⟩)
      (Lev.stepF ⟨K', w, c, dirOf c, scale⟩ F) =
      ∑ B ∈ cube (K' * K') (fun x => cube (K' * K') (fun y => range (2 ^ w x y))),
        ((∏ x ∈ range (K' * K'), F x (B x)) * (2 ^ (scale * nRect K') *
          (if Oth K' w B then 1 else 0))) * rectProd K' w c B := by
    intro c
    refine (Lev.val_step ⟨K', w, c, dirOf c, scale⟩ F).trans (sum_congr rfl fun B hB => ?_)
    have hB' : ∀ x < K' * K', ∀ y < K' * K', B x y < 2 ^ w x y := by
      intro x hx y hy
      have h1 := (mem_cube.1 hB).1 x hx
      exact mem_range.1 ((mem_cube.1 h1).1 y hy)
    have hR := Lev.R_eq ⟨K', w, c, dirOf c, scale⟩ hsym hscale B hB'
    rw [hR]
    ring
  simp only [hval]
  have hsum : ∀ c, (if validCode K' c then
      ∑ B ∈ cube (K' * K') (fun x => cube (K' * K') (fun y => range (2 ^ w x y))),
        ((∏ x ∈ range (K' * K'), F x (B x)) * (2 ^ (scale * nRect K') *
          (if Oth K' w B then 1 else 0))) * rectProd K' w c B else 0) =
      ∑ B ∈ cube (K' * K') (fun x => cube (K' * K') (fun y => range (2 ^ w x y))),
        ((∏ x ∈ range (K' * K'), F x (B x)) * (2 ^ (scale * nRect K') *
          (if Oth K' w B then 1 else 0))) *
          if validCode K' c then rectProd K' w c B else 0 := by
    intro c
    split_ifs
    · rfl
    · simp
  simp only [hsum]
  rw [sum_comm]
  unfold val
  rw [mul_sum]
  refine sum_congr rfl fun B _ => ?_
  rw [← mul_sum]
  have hcode : ∑ c ∈ range (2 ^ K' ^ 4), (if validCode K' c then rectProd K' w c B else 0) =
      prod4 K' (fun a a' b b' => if a < a' ∧ b < b' then rectX K' w B a a' b b' else 1) := by
    unfold rectProd
    rw [sum_code K' (rectP K' w B)]
    simp only [rectP_add]
  rw [hcode, mul_assoc, mul_assoc, oth_mul_cross hsym B]
  ring

end UncrossingWires
