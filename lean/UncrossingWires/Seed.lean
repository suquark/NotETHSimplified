import UncrossingWires.Cube

/-!
# Uncrossing one rectangle

Four numbers `x`, `y`, `u`, `v` hold `m` bits each. The crossing `[x = v] [y = u]` is a product of `U j - S j`, one per
position. Expanding the product gives one term per set `I` of positions, and `Ppol` collects the terms with many, or
with few, positions in `I`. The two collections add up to the crossing (`Ppol_add`).

Each collection is written as a sum over a number `ξ` of a product of one function of `x, y` and one function of `u, v`
(the rows, `dir = true`), or of one function of `x, u` and one function of `y, v` (the columns, `dir = false`). The
number `ξ` has `dLen` bits (`seed_sum`). For the rows the collection with many positions needs few bits; for the columns
the collection with few positions needs few bits (`dLen_le`).
-/

namespace UncrossingWires

open Finset

/-! ### The pieces -/

/-- `s(a, b) = [a ≠ b] (-1) ^ a`. -/
def sgn (a b : Bool) : ℤ := if a = b then 0 else if a then -1 else 1

/-- `U = [x = u] [y = v]`. -/
def Upos (x y u v : Bool) : ℤ := if x = u ∧ y = v then 1 else 0

/-- `S = s(x, y) s(u, v)`. -/
def Spos (x y u v : Bool) : ℤ := sgn x y * sgn u v

/-- The threshold on the size of `I`. -/
def thr (m : ℕ) : ℕ := (m + 1) / 2

/-- The condition on the size of `I`: `pol = true` is the piece with many positions. -/
def condP (pol : Bool) (m r : ℕ) : Prop := if pol then thr m ≤ r else r < thr m

instance (pol : Bool) (m r : ℕ) : Decidable (condP pol m r) := by
  unfold condP
  cases pol <;> simp only [Bool.false_eq_true, if_true, if_false] <;> infer_instance

/-- The term of `I`, for the positions below `m`. -/
def termI (I : Finset ℕ) (m x y u v : ℕ) : ℤ :=
  ∏ j ∈ range m, if j ∈ I then - Spos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)
    else Upos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)

/-- One of the two pieces of the crossing. -/
def Ppol (pol : Bool) (m x y u v : ℕ) : ℤ :=
  ∑ I ∈ (range m).powerset, if condP pol m I.card then termI I m x y u v else 0

/-- The crossing of `m`-bit numbers. -/
def cross (x y u v : ℕ) : ℤ := if x = v ∧ y = u then 1 else 0

/-! The sum over the sets `I`, weighted by a function of the size of `I`, in one recursion on the top position. -/

/-- The sum over the sets `I` of positions below `m`, with the weight `f` on the size of `I`, the factor `a j` for the
positions in `I` and the factor `b j` for the other positions. -/
private def PI (f a b : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ I ∈ (range m).powerset, f I.card * ∏ j ∈ range m, if j ∈ I then a j else b j

private theorem PI_succ (f a b : ℕ → ℤ) (m : ℕ) :
    PI f a b (m + 1) = b m * PI f a b m + a m * PI (fun r => f (r + 1)) a b m := by
  unfold PI
  rw [Finset.range_add_one, Finset.sum_powerset_insert Finset.notMem_range_self, Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun I hI => ?_
    have hmI : m ∉ I := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert Finset.notMem_range_self]
    simp only [hmI, if_false]
    ring
  · refine Finset.sum_congr rfl fun I hI => ?_
    have hmI : m ∉ I := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp hI h)
    rw [Finset.prod_insert Finset.notMem_range_self, Finset.card_insert_of_notMem hmI]
    have hp : ∏ j ∈ range m, (if j ∈ insert m I then a j else b j) =
        ∏ j ∈ range m, (if j ∈ I then a j else b j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjm : j ≠ m := (Finset.mem_range.mp hj).ne
      simp [Finset.mem_insert, hjm]
    rw [hp]
    simp only [Finset.mem_insert_self, if_true]
    ring

private theorem PI_one (a b : ℕ → ℤ) (m : ℕ) :
    PI (fun _ => 1) a b m = ∏ j ∈ range m, (a j + b j) := by
  induction m with
  | zero => simp [PI]
  | succ m ih =>
    rw [PI_succ, Finset.prod_range_succ, ih]
    ring

private theorem pos_cross (a b c d : Bool) :
    -Spos a b c d + Upos a b c d = if a = d ∧ b = c then 1 else 0 := by
  revert a b c d
  decide

private theorem eq_of_testBit_below {m a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : ∀ j ∈ range m, a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < m
  · exact h j (Finset.mem_range.mpr hj)
  · have hle : 2 ^ m ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.not_lt.mp hj)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

/-- The two pieces add up to the crossing. -/
theorem Ppol_add {m x y u v : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ m) (hu : u < 2 ^ m) (hv : v < 2 ^ m) :
    Ppol true m x y u v + Ppol false m x y u v = cross x y u v := by
  have h1 : Ppol true m x y u v + Ppol false m x y u v =
      PI (fun _ => 1) (fun j => -Spos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j))
        (fun j => Upos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)) m := by
    unfold Ppol PI termI
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases h : thr m ≤ I.card
    · simp [condP, h]
    · simp [condP, h, Nat.not_le.mp h]
  rw [h1, PI_one]
  simp only [pos_cross]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one]
  unfold cross
  by_cases hc : x = v ∧ y = u
  · have hall : ∀ j ∈ range m, x.testBit j = v.testBit j ∧ y.testBit j = u.testBit j := by
      intro j _
      rw [hc.1, hc.2]
      exact ⟨rfl, rfl⟩
    rw [if_pos hall, if_pos hc]
  · have hall : ¬ ∀ j ∈ range m, x.testBit j = v.testBit j ∧ y.testBit j = u.testBit j := by
      intro hall
      exact hc ⟨eq_of_testBit_below hx hv fun j hj => (hall j hj).1,
        eq_of_testBit_below hy hu fun j hj => (hall j hj).2⟩
    rw [if_neg hall, if_neg hc]

/-- The piece, in the coordinates of a direction: `(p, q)` is one side and `(r, s)` the other. -/
def PP (dir pol : Bool) (m p q r s : ℕ) : ℤ :=
  if dir then Ppol pol m p q r s else Ppol pol m p r q s

/-! ### The basis -/

/-- The four functions of two bits. -/
def chi : ℕ → Bool → Bool → ℤ
  | 0, a, b => if a = b then 1 else 0
  | 1, a, b => if a = b then 0 else 1
  | 2, a, b => if a = b then (if a then -1 else 1) else 0
  | _, a, b => if a = b then 0 else (if a then -1 else 1)

/-- The product of `chi` over the positions, for a string `π` of letters. -/
def fpat (m : ℕ) (π : ℕ → ℕ) (p q : ℕ) : ℤ :=
  ∏ j ∈ range m, chi (π j) (p.testBit j) (q.testBit j)

/-- The number of letters `l` of `π`. -/
def cnt (m : ℕ) (π : ℕ → ℕ) (l : ℕ) : ℕ := ∑ j ∈ range m, if π j = l then 1 else 0

/-- The coefficient of a string of letters across the rows. -/
def coefR (pol : Bool) (m n3 : ℕ) : ℤ :=
  ∑ r ∈ range (n3 + 1), if condP pol m r then (n3.choose r : ℤ) * (-2) ^ r else 0

/-- The coefficient of a string of letters across the columns. -/
def coefC (pol : Bool) (m n0 n3 : ℕ) : ℤ :=
  (-1) ^ n3 * ∑ r ∈ range (n0 + 1),
    if condP pol m (m - n0 + r) then (n0.choose r : ℤ) * 2 ^ (n0 - r) * (-1) ^ r else 0

/-- The coefficient, for a direction. -/
def rectCoef (dir pol : Bool) (m : ℕ) (π : ℕ → ℕ) : ℤ :=
  if dir then coefR pol m (cnt m π 3) else coefC pol m (cnt m π 0) (cnt m π 3)

/-! The expansion of a term of `Ppol` in the basis `chi`. -/

private theorem two_pow_termI (a b : ℕ → ℤ) (m x y u v p q r s : ℕ) (I : Finset ℕ)
    (hS : ∀ j, 2 * (-Spos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)) =
      ∑ c ∈ range 4, a c * (chi c (p.testBit j) (q.testBit j) * chi c (r.testBit j) (s.testBit j)))
    (hU : ∀ j, 2 * Upos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j) =
      ∑ c ∈ range 4, b c * (chi c (p.testBit j) (q.testBit j) * chi c (r.testBit j) (s.testBit j))) :
    2 ^ m * termI I m x y u v =
      ∑ π ∈ cube m (fun _ => range 4),
        (∏ j ∈ range m, if j ∈ I then a (π j) else b (π j)) * (fpat m π p q * fpat m π r s) := by
  have h := sum_cube_prod m (fun _ => range 4) (fun j c => (if j ∈ I then a c else b c) *
    (chi c (p.testBit j) (q.testBit j) * chi c (r.testBit j) (s.testBit j)))
  have hL : 2 ^ m * termI I m x y u v =
      ∏ j ∈ range m, ∑ c ∈ range 4, (if j ∈ I then a c else b c) *
        (chi c (p.testBit j) (q.testBit j) * chi c (r.testBit j) (s.testBit j)) := by
    unfold termI
    have h2 : (2 : ℤ) ^ m = ∏ _j ∈ range m, 2 := by simp
    rw [h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j ∈ I
    · simp only [hj, if_true]
      exact hS j
    · simp only [hj, if_false]
      exact hU j
  rw [hL, ← h]
  refine Finset.sum_congr rfl fun π _ => ?_
  unfold fpat
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

private theorem expand_piece (pol : Bool) (a b : ℕ → ℤ) (m x y u v p q r s : ℕ)
    (hS : ∀ j, 2 * (-Spos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j)) =
      ∑ c ∈ range 4, a c * (chi c (p.testBit j) (q.testBit j) * chi c (r.testBit j) (s.testBit j)))
    (hU : ∀ j, 2 * Upos (x.testBit j) (y.testBit j) (u.testBit j) (v.testBit j) =
      ∑ c ∈ range 4, b c * (chi c (p.testBit j) (q.testBit j) * chi c (r.testBit j) (s.testBit j))) :
    2 ^ m * Ppol pol m x y u v =
      ∑ π ∈ cube m (fun _ => range 4),
        PI (fun t => if condP pol m t then 1 else 0) (fun j => a (π j)) (fun j => b (π j)) m *
          fpat m π p q * fpat m π r s := by
  unfold Ppol
  rw [Finset.mul_sum]
  have hterm : ∀ I ∈ (range m).powerset,
      2 ^ m * (if condP pol m I.card then termI I m x y u v else 0) =
        ∑ π ∈ cube m (fun _ => range 4), (if condP pol m I.card then 1 else 0) *
          ((∏ j ∈ range m, if j ∈ I then a (π j) else b (π j)) * (fpat m π p q * fpat m π r s)) := by
    intro I _
    rw [← Finset.mul_sum, ← two_pow_termI a b m x y u v p q r s I hS hU]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  unfold PI
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun I _ => ?_
  ring

/-! The weights of the letters. -/

private def aR (c : ℕ) : ℤ := if c = 3 then -2 else 0

private def bR (_ : ℕ) : ℤ := 1

private def aC (c : ℕ) : ℤ := if c = 1 ∨ c = 2 then 1 else -1

private def bC (c : ℕ) : ℤ := if c = 0 then 2 else 0

private theorem pos_rows_S (a b c d : Bool) :
    2 * (-Spos a b c d) = ∑ l ∈ range 4, aR l * (chi l a b * chi l c d) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  revert a b c d
  decide

private theorem pos_rows_U (a b c d : Bool) :
    2 * Upos a b c d = ∑ l ∈ range 4, bR l * (chi l a b * chi l c d) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  revert a b c d
  decide

private theorem pos_cols_S (a b c d : Bool) :
    2 * (-Spos a b c d) = ∑ l ∈ range 4, aC l * (chi l a c * chi l b d) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  revert a b c d
  decide

private theorem pos_cols_U (a b c d : Bool) :
    2 * Upos a b c d = ∑ l ∈ range 4, bC l * (chi l a c * chi l b d) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  revert a b c d
  decide

private theorem cnt_succ (m : ℕ) (π : ℕ → ℕ) (l : ℕ) :
    cnt (m + 1) π l = cnt m π l + if π m = l then 1 else 0 :=
  Finset.sum_range_succ _ _

private theorem cnt_le (m : ℕ) (π : ℕ → ℕ) (l : ℕ) : cnt m π l ≤ m := by
  induction m with
  | zero => simp [cnt]
  | succ m ih =>
    rw [cnt_succ]
    split_ifs <;> omega

/-- Pascal's rule for a sum with binomial weights. -/
private theorem sum_choose_succ (n : ℕ) (h : ℕ → ℤ) :
    ∑ r ∈ range (n + 2), ((n + 1).choose r : ℤ) * h r =
      ∑ r ∈ range (n + 1), (n.choose r : ℤ) * h r +
        ∑ r ∈ range (n + 1), (n.choose r : ℤ) * h (r + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ' (fun r => (n.choose r : ℤ) * h r) n]
  have h1 : ∑ r ∈ range (n + 1), ((n + 1).choose (r + 1) : ℤ) * h (r + 1) =
      ∑ r ∈ range (n + 1), (n.choose r : ℤ) * h (r + 1) +
        ∑ r ∈ range (n + 1), (n.choose (r + 1) : ℤ) * h (r + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [h1, Finset.sum_range_succ (fun r => (n.choose (r + 1) : ℤ) * h (r + 1)) n]
  simp
  ring

private theorem PI_rows (π : ℕ → ℕ) (m : ℕ) (f : ℕ → ℤ) :
    PI f (fun j => aR (π j)) (fun j => bR (π j)) m =
      ∑ r ∈ range (cnt m π 3 + 1), ((cnt m π 3).choose r : ℤ) * ((-2) ^ r * f r) := by
  induction m generalizing f with
  | zero => simp [PI, cnt]
  | succ m ih =>
    rw [PI_succ, ih, ih]
    by_cases hm : π m = 3
    · have hc : cnt (m + 1) π 3 = cnt m π 3 + 1 := by simp [cnt_succ, hm]
      rw [hc, sum_choose_succ, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun r _ => ?_
        simp [bR]
      · refine Finset.sum_congr rfl fun r _ => ?_
        simp only [aR, hm, if_true]
        ring
    · have hc : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      rw [hc]
      simp [aR, bR, hm]

private theorem PI_cols (π : ℕ → ℕ) (m : ℕ) (hπ : ∀ j < m, π j < 4) (f : ℕ → ℤ) :
    PI f (fun j => aC (π j)) (fun j => bC (π j)) m =
      (-1) ^ cnt m π 3 * ∑ r ∈ range (cnt m π 0 + 1),
        ((cnt m π 0).choose r : ℤ) * (2 ^ (cnt m π 0 - r) * (-1) ^ r * f (m - cnt m π 0 + r)) := by
  induction m generalizing f with
  | zero => simp [PI, cnt]
  | succ m ih =>
    have hπ' : ∀ j < m, π j < 4 := fun j hj => hπ j (Nat.lt_succ_of_lt hj)
    have h4 := hπ m (Nat.lt_succ_self m)
    have hn := cnt_le m π 0
    rw [PI_succ, ih hπ', ih hπ']
    have hsum : ∑ r ∈ range (cnt m π 0 + 1),
          ((cnt m π 0).choose r : ℤ) * (2 ^ (cnt m π 0 - r) * (-1) ^ r * f (m + 1 - cnt m π 0 + r)) =
        ∑ r ∈ range (cnt m π 0 + 1),
          ((cnt m π 0).choose r : ℤ) * (2 ^ (cnt m π 0 - r) * (-1) ^ r * f (m - cnt m π 0 + r + 1)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have e : m + 1 - cnt m π 0 + r = m - cnt m π 0 + r + 1 := by omega
      rw [e]
    rcases (by omega : π m = 0 ∨ π m = 3 ∨ π m = 1 ∨ π m = 2) with hm | hm | hm | hm
    · have hc0 : cnt (m + 1) π 0 = cnt m π 0 + 1 := by simp [cnt_succ, hm]
      have hc3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ha : aC (π m) = -1 := by simp [aC, hm]
      have hb : bC (π m) = 2 := by simp [bC, hm]
      have hsum1 : ∑ r ∈ range (cnt m π 0 + 1), ((cnt m π 0).choose r : ℤ) *
            (2 ^ (cnt m π 0 + 1 - r) * (-1) ^ r * f (m + 1 - (cnt m π 0 + 1) + r)) =
          2 * ∑ r ∈ range (cnt m π 0 + 1),
            ((cnt m π 0).choose r : ℤ) * (2 ^ (cnt m π 0 - r) * (-1) ^ r * f (m - cnt m π 0 + r)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr' := Finset.mem_range.mp hr
        have e1 : cnt m π 0 + 1 - r = (cnt m π 0 - r) + 1 := by omega
        have e2 : m + 1 - (cnt m π 0 + 1) = m - cnt m π 0 := by omega
        rw [e1, e2, pow_succ]
        ring
      have hsum2 : ∑ r ∈ range (cnt m π 0 + 1), ((cnt m π 0).choose r : ℤ) *
            (2 ^ (cnt m π 0 + 1 - (r + 1)) * (-1) ^ (r + 1) * f (m + 1 - (cnt m π 0 + 1) + (r + 1))) =
          -∑ r ∈ range (cnt m π 0 + 1),
            ((cnt m π 0).choose r : ℤ) * (2 ^ (cnt m π 0 - r) * (-1) ^ r * f (m - cnt m π 0 + r + 1)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun r _ => ?_
        have e1 : cnt m π 0 + 1 - (r + 1) = cnt m π 0 - r := by omega
        have e2 : m + 1 - (cnt m π 0 + 1) + (r + 1) = m - cnt m π 0 + r + 1 := by omega
        rw [e1, e2, pow_succ]
        ring
      rw [hc0, hc3, sum_choose_succ, hsum1, hsum2, ha, hb]
      ring
    · have hc0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have hc3 : cnt (m + 1) π 3 = cnt m π 3 + 1 := by simp [cnt_succ, hm]
      have ha : aC (π m) = -1 := by simp [aC, hm]
      have hb : bC (π m) = 0 := by simp [bC, hm]
      rw [hc0, hc3, hsum, ha, hb, pow_succ]
      ring
    · have hc0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have hc3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ha : aC (π m) = 1 := by simp [aC, hm]
      have hb : bC (π m) = 0 := by simp [bC, hm]
      rw [hc0, hc3, hsum, ha, hb]
      ring
    · have hc0 : cnt (m + 1) π 0 = cnt m π 0 := by simp [cnt_succ, hm]
      have hc3 : cnt (m + 1) π 3 = cnt m π 3 := by simp [cnt_succ, hm]
      have ha : aC (π m) = 1 := by simp [aC, hm]
      have hb : bC (π m) = 0 := by simp [bC, hm]
      rw [hc0, hc3, hsum, ha, hb]
      ring

/-- Across the rows, the piece is a sum over strings of letters, up to the factor `2 ^ m`. -/
theorem seed_rows (pol : Bool) (m x y u v : ℕ) :
    2 ^ m * Ppol pol m x y u v =
      ∑ π ∈ cube m (fun _ => range 4), rectCoef true pol m π * fpat m π x y * fpat m π u v := by
  rw [expand_piece pol aR bR m x y u v x y u v (fun j => pos_rows_S _ _ _ _)
    (fun j => pos_rows_U _ _ _ _)]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [PI_rows]
  congr 2
  simp only [rectCoef, coefR, if_true]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

/-- Across the columns, the piece is a sum over strings of letters, up to the factor `2 ^ m`. -/
theorem seed_cols (pol : Bool) (m x y u v : ℕ) :
    2 ^ m * Ppol pol m x y u v =
      ∑ π ∈ cube m (fun _ => range 4), rectCoef false pol m π * fpat m π x u * fpat m π y v := by
  rw [expand_piece pol aC bC m x y u v x u y v (fun j => pos_cols_S _ _ _ _)
    (fun j => pos_cols_U _ _ _ _)]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hπ4 : ∀ j < m, π j < 4 := by
    rw [mem_cube] at hπ
    exact fun j hj => Finset.mem_range.mp (hπ.1 j hj)
  rw [PI_cols π m hπ4]
  congr 2
  simp only [rectCoef, coefC, Bool.false_eq_true, if_false]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs
  · rw [mul_one]
    ring
  · simp

/-! ### The number of bits -/

/-- The width of the index. `cheap` is the direction in which the piece has few strings of letters. -/
def dLen (cheap : Bool) (m : ℕ) : ℕ := if cheap then m + (8 * (m / 2) + 4) / 5 else 2 * m

/-- The number of paired wires of two diagonals: the largest odd number up to the minimum, or zero. -/
def oddMin (a b : ℕ) : ℕ := if min a b = 0 then 0 else if min a b % 2 = 1 then min a b else min a b - 1

/-- The number of set bits of `M` below `j`. -/
def popB (M j : ℕ) : ℕ := ∑ i ∈ range j, (M.testBit i).toNat

/-- The letter `j` of the index `ξ`, when all letters have two bits. -/
def letterPlain (ξ j : ℕ) : ℕ := ξ / 4 ^ j % 4

/-- The letter `j` of the index `ξ`, in the short code. The low `m` bits mark the letters `3` (rows) or `0` (columns).
The other letters are the digits of the high part in base `3`. -/
def letterCheap (dir : Bool) (m ξ j : ℕ) : ℕ :=
  if (ξ % 2 ^ m).testBit j then (if dir then 3 else 0)
  else
    (ξ / 2 ^ m / 3 ^ (j - popB (ξ % 2 ^ m) j) % 3) + (if dir then 0 else 1)

/-- The string of letters of an index. -/
def letterOf (cheap dir : Bool) (m ξ j : ℕ) : ℕ :=
  if j < m then (if cheap then letterCheap dir m ξ j else letterPlain ξ j) else 0

/-- An index of the short code is valid if its high part has no extra digit. -/
def validIdx (cheap : Bool) (m ξ : ℕ) : Prop :=
  cheap = true → ξ / 2 ^ m < 3 ^ (m - popB (ξ % 2 ^ m) m)

instance (cheap : Bool) (m ξ : ℕ) : Decidable (validIdx cheap m ξ) := by
  unfold validIdx
  infer_instance

/-- The function of one side of the rectangle: the side `u` of a pair `u < u'`. It holds the scale and the coefficient. -/
def rectA (dir pol : Bool) (scale m ξ p q : ℕ) : ℤ :=
  if validIdx (pol == dir) m ξ then
    2 ^ (scale - m) * rectCoef dir pol m (letterOf (pol == dir) dir m ξ) *
      fpat m (letterOf (pol == dir) dir m ξ) p q
  else 0

/-- The function of the other side of the rectangle. -/
def rectB (dir pol : Bool) (m ξ r s : ℕ) : ℤ :=
  if validIdx (pol == dir) m ξ then fpat m (letterOf (pol == dir) dir m ξ) r s else 0

/-! The sum over the indices of the short code. -/

private theorem three_pow_le (k : ℕ) : 3 ^ k ≤ 2 ^ ((8 * k + 4) / 5) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 5
    · interval_cases k <;> norm_num
    · obtain ⟨t, rfl⟩ : ∃ t, k = t + 5 := ⟨k - 5, by omega⟩
      have h1 := ih t (by omega)
      have h2 : (8 * (t + 5) + 4) / 5 = (8 * t + 4) / 5 + 8 := by omega
      rw [h2, pow_add, pow_add]
      calc 3 ^ t * 3 ^ 5 ≤ 2 ^ ((8 * t + 4) / 5) * 3 ^ 5 := Nat.mul_le_mul_right _ h1
        _ ≤ 2 ^ ((8 * t + 4) / 5) * 2 ^ 8 := Nat.mul_le_mul_left _ (by norm_num)

private theorem popB_succ (M j : ℕ) : popB M (j + 1) = popB M j + (M.testBit j).toNat :=
  Finset.sum_range_succ _ _

private theorem popB_le (M j : ℕ) : popB M j ≤ j := by
  induction j with
  | zero => simp [popB]
  | succ j ih =>
    rw [popB_succ]
    have := Bool.toNat_le (M.testBit j)
    omega

private theorem popB_gap {M j m : ℕ} (hj : j < m) (hb : M.testBit j = false) :
    popB M m + j + 1 ≤ popB M j + m := by
  induction m, Nat.succ_le_of_lt hj using Nat.le_induction with
  | base => simp [popB_succ, hb]
  | succ m hm ih =>
    rw [popB_succ]
    have := Bool.toNat_le (M.testBit m)
    have := ih (Nat.lt_of_succ_le hm)
    omega

private theorem popB_congr {M M' j : ℕ} (h : ∀ i < j, M.testBit i = M'.testBit i) :
    popB M j = popB M' j :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

/-- The letters given by the mark `M` and the digits `c`. -/
private def lettersOf (dir : Bool) (m M c j : ℕ) : ℕ :=
  if j < m then
    if M.testBit j then (if dir then 3 else 0)
    else (c / 3 ^ (j - popB M j) % 3) + (if dir then 0 else 1)
  else 0

private theorem digit_low {i N : ℕ} (hi : i < N) (c0 d : ℕ) :
    (c0 + 3 ^ N * d) / 3 ^ i % 3 = c0 / 3 ^ i % 3 := by
  obtain ⟨e, rfl⟩ : ∃ e, N = i + 1 + e := ⟨N - (i + 1), by omega⟩
  rw [pow_add, pow_succ, mul_assoc, mul_assoc, Nat.add_mul_div_left _ _ (by positivity),
    Nat.add_mul_mod_self_left]

private theorem letters_zero (dir : Bool) {m M c0 d : ℕ} (hM : M < 2 ^ m)
    (hc : c0 < 3 ^ (m - popB M m)) (hd : d < 3) :
    lettersOf dir (m + 1) M (c0 + 3 ^ (m - popB M m) * d) =
      Function.update (lettersOf dir m M c0) m (d + if dir then 0 else 1) := by
  funext j
  rcases lt_trichotomy j m with h | rfl | h
  · rw [Function.update_of_ne h.ne]
    simp only [lettersOf, h, Nat.lt_succ_of_lt h, if_true]
    by_cases hb : M.testBit j = true
    · simp [hb]
    · have hb' : M.testBit j = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, if_false]
      have h1 := popB_gap h hb'
      have h2 := popB_le M j
      have h3 := popB_le M m
      rw [digit_low (by omega)]
  · have hb : M.testBit j = false := Nat.testBit_lt_two_pow hM
    simp only [lettersOf, Nat.lt_succ_self, if_true, Function.update_self, hb, Bool.false_eq_true,
      if_false]
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hc, Nat.zero_add,
      Nat.mod_eq_of_lt hd]
  · rw [Function.update_of_ne h.ne']
    simp [lettersOf, Nat.not_lt.mpr h.le, Nat.not_lt.mpr (Nat.succ_le_of_lt h)]

private theorem letters_one (dir : Bool) {m M : ℕ} (hM : M < 2 ^ m) (c : ℕ) :
    popB (M + 2 ^ m * 1) (m + 1) = popB M m + 1 ∧
    lettersOf dir (m + 1) (M + 2 ^ m * 1) c =
      Function.update (lettersOf dir m M c) m (if dir then 3 else 0) := by
  have hbit : ∀ j < m, (M + 2 ^ m * 1).testBit j = M.testBit j := by
    intro j hj
    rw [mul_one, Nat.add_comm, Nat.testBit_two_pow_add_gt hj]
  have hpop : ∀ j ≤ m, popB (M + 2 ^ m * 1) j = popB M j :=
    fun j hj => popB_congr fun i hi => hbit i (by omega)
  have htop : (M + 2 ^ m * 1).testBit m = true := by
    rw [mul_one, Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hM]
    rfl
  refine ⟨?_, ?_⟩
  · rw [popB_succ, hpop m le_rfl, htop]
    rfl
  · funext j
    rcases lt_trichotomy j m with h | rfl | h
    · rw [Function.update_of_ne h.ne]
      simp only [lettersOf, h, Nat.lt_succ_of_lt h, if_true, hbit j h, hpop j h.le]
    · simp only [lettersOf, Nat.lt_succ_self, if_true, htop, Function.update_self]
    · rw [Function.update_of_ne h.ne']
      simp [lettersOf, Nat.not_lt.mpr h.le, Nat.not_lt.mpr (Nat.succ_le_of_lt h)]

private theorem sum_range_mul_aux {β : Type*} [AddCommMonoid β] (A B : ℕ) (G : ℕ → β) :
    ∑ Z ∈ range (A * B), G Z = ∑ y ∈ range B, ∑ x ∈ range A, G (x + A * y) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.add_comm]

private theorem sum_four {β : Type*} [AddCommMonoid β] (dir : Bool) (h : ℕ → β) :
    ∑ x ∈ range 4, h x =
      ∑ d ∈ range 3, h (d + if dir then 0 else 1) + h (if dir then 3 else 0) := by
  cases dir
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, Bool.false_eq_true, if_false]
    abel
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, if_true]

/-- The strings of letters are in bijection with the marks and their digits. -/
private theorem sum_letters {β : Type*} [AddCommMonoid β] (dir : Bool) (m : ℕ)
    (G : (ℕ → ℕ) → β) :
    ∑ M ∈ range (2 ^ m), ∑ c ∈ range (3 ^ (m - popB M m)), G (lettersOf dir m M c) =
      ∑ π ∈ cube m (fun _ => range 4), G π := by
  induction m generalizing G with
  | zero =>
    have hc : cube 0 (fun _ => range 4) = ({0} : Finset (ℕ → ℕ)) := by
      ext f
      simp [mem_cube, funext_iff]
    have hl : lettersOf dir 0 0 0 = 0 := by
      funext j
      simp [lettersOf]
    simp [hc, popB, hl]
  | succ m ih =>
    rw [sum_cube_succ, ← ih (fun π => ∑ x ∈ range 4, G (Function.update π m x)), sum_split m 1,
      pow_one, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M hM => ?_
    have hM' := Finset.mem_range.mp hM
    have hbit : M.testBit m = false := Nat.testBit_lt_two_pow hM'
    have hp := popB_le M m
    have h0 : ∑ c ∈ range (3 ^ (m + 1 - popB (M + 2 ^ m * 0) (m + 1))),
          G (lettersOf dir (m + 1) (M + 2 ^ m * 0) c) =
        ∑ d ∈ range 3, ∑ c0 ∈ range (3 ^ (m - popB M m)),
          G (Function.update (lettersOf dir m M c0) m (d + if dir then 0 else 1)) := by
      have e1 : M + 2 ^ m * 0 = M := by simp
      have e2 : m + 1 - popB M (m + 1) = (m - popB M m) + 1 := by
        rw [popB_succ, hbit]
        simp only [Bool.toNat_false, add_zero]
        omega
      rw [e1, e2, pow_succ, sum_range_mul_aux]
      refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun c0 hc0 => ?_
      rw [letters_zero dir hM' (Finset.mem_range.mp hc0) (Finset.mem_range.mp hd)]
    have h1 : ∑ c ∈ range (3 ^ (m + 1 - popB (M + 2 ^ m * 1) (m + 1))),
          G (lettersOf dir (m + 1) (M + 2 ^ m * 1) c) =
        ∑ c ∈ range (3 ^ (m - popB M m)),
          G (Function.update (lettersOf dir m M c) m (if dir then 3 else 0)) := by
      have e2 : m + 1 - popB (M + 2 ^ m * 1) (m + 1) = m - popB M m := by
        rw [(letters_one dir hM' 0).1]
        omega
      rw [e2]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [(letters_one dir hM' c).2]
    rw [h0, h1, Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sum_four dir (fun x => G (Function.update (lettersOf dir m M c) m x))]

private theorem cnt_letters (dir : Bool) (m M c : ℕ) :
    cnt m (lettersOf dir m M c) (if dir then 3 else 0) = popB M m := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  by_cases hb : M.testBit j = true
  · simp [lettersOf, hj', hb]
  · have hb' : M.testBit j = false := by simpa using hb
    have hd := Nat.mod_lt (c / 3 ^ (j - popB M j)) (by norm_num : 3 > 0)
    cases dir
    · simp [lettersOf, hj', hb']
    · simp [lettersOf, hj', hb']
      omega

/-- The sum over the indices of the short code. The strings of letters with many non-special letters have no index, but
they do not count: `G` vanishes on them. -/
private theorem sum_cheap (dir : Bool) (m : ℕ) (G : (ℕ → ℕ) → ℤ)
    (hG : ∀ π, m / 2 < m - cnt m π (if dir then 3 else 0) → G π = 0) :
    ∑ ξ ∈ range (2 ^ dLen true m), (if validIdx true m ξ then G (letterOf true dir m ξ) else 0) =
      ∑ π ∈ cube m (fun _ => range 4), G π := by
  rw [← sum_letters dir m G]
  have hd : dLen true m = m + (8 * (m / 2) + 4) / 5 := by simp [dLen]
  rw [hd, sum_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun M hM => ?_
  have hM' := Finset.mem_range.mp hM
  have ht : ∀ c, (if validIdx true m (M + 2 ^ m * c) then G (letterOf true dir m (M + 2 ^ m * c))
      else 0) = if c < 3 ^ (m - popB M m) then G (lettersOf dir m M c) else 0 := by
    intro c
    have h1 : (M + 2 ^ m * c) % 2 ^ m = M := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hM']
    have h2 : (M + 2 ^ m * c) / 2 ^ m = c := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hM', Nat.zero_add]
    have h3 : letterOf true dir m (M + 2 ^ m * c) = lettersOf dir m M c := by
      funext j
      simp only [letterOf, letterCheap, lettersOf, h1, h2, if_true]
    have h4 : validIdx true m (M + 2 ^ m * c) ↔ c < 3 ^ (m - popB M m) := by
      simp only [validIdx, h1, h2, forall_const]
    simp only [h3, h4]
  simp only [ht]
  by_cases hsmall : m - popB M m ≤ m / 2
  · have hN : 3 ^ (m - popB M m) ≤ 2 ^ ((8 * (m / 2) + 4) / 5) :=
      (Nat.pow_le_pow_right (by norm_num) hsmall).trans (three_pow_le _)
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · have hz : ∀ c, G (lettersOf dir m M c) = 0 := fun c => hG _ (by
      rw [cnt_letters]
      omega)
    simp [hz]

private theorem sum_plain {β : Type*} [AddCommMonoid β] (dir : Bool) (m : ℕ) (G : (ℕ → ℕ) → β) :
    ∑ ξ ∈ range (2 ^ (2 * m)), G (letterOf false dir m ξ) =
      ∑ π ∈ cube m (fun _ => range 4), G π := by
  have h := sum_viewL m (fun _ => 2) G
  have hs : ∑ _t ∈ range m, 2 = 2 * m := by simp [mul_comm]
  have hv : ∀ ξ, letterOf false dir m ξ = viewL m (fun _ => 2) ξ := by
    intro ξ
    funext j
    by_cases hj : j < m
    · have hs' : ∑ _t ∈ range j, 2 = 2 * j := by simp [mul_comm]
      simp only [letterOf, letterPlain, viewL, hj, if_true, Bool.false_eq_true, if_false, hs',
        pow_mul]
      norm_num
    · simp [letterOf, viewL, hj]
  simp only [hv]
  rw [hs] at h
  exact h

private theorem coefR_true_zero {m n : ℕ} (h : m / 2 < m - n) : coefR true m n = 0 := by
  unfold coefR
  refine Finset.sum_eq_zero fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  have hn : ¬ condP true m r := by
    simp only [condP, if_true, thr]
    omega
  rw [if_neg hn]

private theorem coefC_false_zero {m n0 n3 : ℕ} (h : m / 2 < m - n0) : coefC false m n0 n3 = 0 := by
  unfold coefC
  rw [Finset.sum_eq_zero, mul_zero]
  intro r _
  have hn : ¬ condP false m (m - n0 + r) := by
    simp only [condP, Bool.false_eq_true, if_false, thr]
    omega
  rw [if_neg hn]

/-- The sum over the indices, in both codes. -/
private theorem sum_index (dir pol : Bool) (m p q r s : ℕ) :
    ∑ ξ ∈ range (2 ^ dLen (pol == dir) m), (if validIdx (pol == dir) m ξ then
        rectCoef dir pol m (letterOf (pol == dir) dir m ξ) *
          fpat m (letterOf (pol == dir) dir m ξ) p q * fpat m (letterOf (pol == dir) dir m ξ) r s
      else 0) =
      ∑ π ∈ cube m (fun _ => range 4), rectCoef dir pol m π * fpat m π p q * fpat m π r s := by
  by_cases hc : (pol == dir) = true
  · rw [hc]
    have hpd : pol = dir := by simpa using hc
    subst hpd
    cases pol
    · refine sum_cheap false m (fun π => rectCoef false false m π * fpat m π p q * fpat m π r s)
        fun π hπ => ?_
      simp only [rectCoef, Bool.false_eq_true, if_false] at hπ ⊢
      rw [coefC_false_zero hπ]
      simp
    · refine sum_cheap true m (fun π => rectCoef true true m π * fpat m π p q * fpat m π r s)
        fun π hπ => ?_
      simp only [rectCoef, if_true] at hπ ⊢
      rw [coefR_true_zero hπ]
      simp
  · have hc' : (pol == dir) = false := by simpa using hc
    rw [hc']
    have hv : ∀ ξ, validIdx false m ξ := fun ξ h => by simp at h
    simp only [hv, if_true]
    have hd : dLen false m = 2 * m := by simp [dLen]
    rw [hd]
    exact sum_plain dir m (fun π => rectCoef dir pol m π * fpat m π p q * fpat m π r s)

/-- **The seed.** The piece of the crossing factors through `dLen` bits, for each direction. -/
theorem seed_sum (dir pol : Bool) {scale m : ℕ} (hm : m ≤ scale) (p q r s : ℕ) :
    ∑ ξ ∈ range (2 ^ dLen (pol == dir) m), rectA dir pol scale m ξ p q * rectB dir pol m ξ r s =
      2 ^ scale * PP dir pol m p q r s := by
  have hPP : ∑ π ∈ cube m (fun _ => range 4), rectCoef dir pol m π * fpat m π p q * fpat m π r s =
      2 ^ m * PP dir pol m p q r s := by
    cases dir
    · simp only [PP, Bool.false_eq_true, if_false]
      rw [seed_cols pol m p r q s]
    · simp only [PP, if_true]
      rw [seed_rows pol m p q r s]
  have hterm : ∀ ξ, rectA dir pol scale m ξ p q * rectB dir pol m ξ r s =
      2 ^ (scale - m) * (if validIdx (pol == dir) m ξ then
        rectCoef dir pol m (letterOf (pol == dir) dir m ξ) *
          fpat m (letterOf (pol == dir) dir m ξ) p q * fpat m (letterOf (pol == dir) dir m ξ) r s
      else 0) := by
    intro ξ
    unfold rectA rectB
    split_ifs
    · ring
    · simp
  simp only [hterm]
  rw [← Finset.mul_sum, sum_index, hPP, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]

/-- The width of a pair of diagonals, for `m = oddMin w1 w2`: the two widths are at most `w1 + w2` and
`max w1 w2 + (9 / 10) min w1 w2`. -/
theorem dLen_cheap_le (w1 w2 : ℕ) :
    10 * (w1 + w2 - 2 * oddMin w1 w2 + dLen true (oddMin w1 w2)) ≤ 10 * max w1 w2 + 9 * min w1 w2 := by
  simp only [dLen, oddMin, if_true]
  split_ifs <;> omega

theorem dLen_le (b : Bool) (w1 w2 : ℕ) : dLen b (oddMin w1 w2) ≤ 2 * oddMin w1 w2 := by
  cases b
  · simp [dLen]
  · simp only [dLen, oddMin, if_true]
    split_ifs <;> omega

theorem oddMin_le_left (a b : ℕ) : oddMin a b ≤ a := by
  simp only [oddMin]
  split_ifs <;> omega

theorem oddMin_le_right (a b : ℕ) : oddMin a b ≤ b := by
  simp only [oddMin]
  split_ifs <;> omega

theorem oddMin_comm (a b : ℕ) : oddMin a b = oddMin b a := by
  simp [oddMin, min_comm]

end UncrossingWires
