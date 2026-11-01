import OnePigeonhole.Pseudo.FinalHelpers
import OnePigeonhole.Pseudo.FinalCost
import OnePigeonhole.Pseudo.LeafLits
import OnePigeonhole.Pseudo.GreedySpec

/-!
# The program for one leaf of the branching tree

`leafE m d lt` runs on `encF n G :: p :: root :: enc :: n :: rest`. It computes the network of `G`, the table of its words and the table of its
layers, and then it runs the core program. The value is not zero exactly when `G` is satisfiable (`leaf_main`).

`shape_net`: the network of a formula has the shape of the placement. A wire of the network is a free wire of a variable, or an occurrence of a
variable in a clause. So the number `M` of wires is at least the number `n` of variables, and at most `(1 + d) * n`.
-/

namespace OnePigeonhole.Pseudo.Final

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo TransposeBase.Pseudo.Code SatBase
  OnePigeonhole.Pseudo.Leaf TransposeBase.Pseudo.CnfTree TransposeBase.Pseudo.CnfNet TransposeBase.Sat

/-! ### The shape of the network of a formula -/

section Shape

variable {n : ℕ} {F : ClauseSet (SignedLiteral n)}

/-- The tail of a wire is a variable node. -/
theorem tailN_lt (hF : Wide3 F) (e : Fin (mN n F)) : (tailN hF e : ℕ) < n := by
  obtain ⟨w, rfl⟩ := (eW hF).surjective e
  cases w with
  | inl u =>
    rw [tail_inl]
    exact u.2
  | inr j =>
    rw [tail_inr]
    exact j.2.1.1.2

/-- The head of a wire is not a variable node. -/
theorem le_headN (hF : Wide3 F) (e : Fin (mN n F)) : n ≤ (headN hF e : ℕ) := by
  obtain ⟨w, rfl⟩ := (eW hF).surjective e
  cases w with
  | inl u =>
    rw [head_inl]
    omega
  | inr j =>
    rw [head_inr]
    omega

/-- At most three wires have the same head: a clause has at most three literals, and an end node has one wire. -/
theorem card_hd_le (hF : Wide3 F) (α : Node F) : #{w : Wire F | hd F w = α} ≤ 3 := by
  rcases α with u | e | u
  · have h : ({w | hd F w = .inl u} : Finset (Wire F)) = ∅ := by
      refine filter_eq_empty_iff.mpr fun w _ h => ?_
      cases w <;> simp [hd] at h
    rw [h]
    simp
  · have hcard : #{w : Wire F | hd F w = .inr (.inl e)} ≤ #(univ : Finset (LI F e)) := by
      refine card_le_card_of_surjOn (fun l : LI F e => (.inr ⟨e, l⟩ : Wire F)) ?_
      intro w hw
      have h := (mem_filter.mp (mem_coe.mp hw)).2
      cases w with
      | inl u => simp [hd] at h
      | inr j =>
        obtain ⟨e', l⟩ := j
        simp only [hd, Sum.inr.injEq] at h
        have h' : e' = e := Sum.inl.inj h
        subst h'
        exact ⟨l, by simp, rfl⟩
    have h3 : #(univ : Finset (LI F e)) ≤ 3 := by simpa using hF e.1 e.2
    omega
  · have hsub : ({w | hd F w = .inr (.inr u)} : Finset (Wire F)) ⊆ {.inl u} := by
      intro w hw
      have h := (mem_filter.mp hw).2
      cases w with
      | inl u' =>
        simp only [hd, Sum.inr.injEq] at h
        simp [h]
      | inr j => simp [hd] at h
    have := card_le_card hsub
    simp only [card_singleton] at this
    omega

theorem card_headN_le (hF : Wide3 F) (a : Fin (vN n F)) : #{e | headN hF e = a} ≤ 3 := by
  have h : #{e | headN hF e = a} = #{w : Wire F | hd F w = (eN hF).symm a} := by
    refine Finset.card_equiv (eW hF).symm fun e => ?_
    rw [mem_filter, mem_filter]
    simp only [mem_univ, true_and, headN, Equiv.eq_symm_apply]
  rw [h]
  exact card_hd_le hF _

/-- The network of a formula has the shape of the placement. -/
theorem shape_net (hF : Wide3 F) {D : ℕ} (harity : ∀ α, Spread.arity (tailN hF) (headN hF) α ≤ D) :
    Greedy.Shape n D (tailN hF) (headN hF) where
  tail_lt := tailN_lt hF
  le_head := le_headN hF
  card_tail a := (card_le_card fun _ he =>
    mem_filter.mpr ⟨mem_univ _, Or.inl (mem_filter.mp he).2⟩).trans (harity a)
  card_head := card_headN_le hF

end Shape

/-! ### The program -/

/-- The number of words, for the parameter `m`. -/
abbrev Kof (m : ℕ) : ℕ := (6 * m ^ 4) ^ m ^ 4

/-- The node program in the environment of `leafE`: the leaf word is variable `18`, and `n` is variable `22`. -/
def leafNode : Expr := CnfNet.nodeE 22 18

/-- The program of a leaf. It binds the values in the order that they need, then it copies them to the interface order of `coreE`. The last
addition reduces the value below `2 ^ W`. -/
def leafE (m d : ℕ) (lt : Lits) : Expr :=
  .letE (mE 4 0) <| .letE (vE 5 1) <| .letE (fwE (Kof m) 1 0) <| .letE (tailTE 7 3 0) <|
  .letE (headTE 8 4 1) <| .letE (greedyE (m ^ 4) (6 * m ^ 4) 9 4 3 2 1 0) <|
  .letE (hE (Kof m) (1 + d) 10) <| .letE (layTE 6 3 2 4 1) <|
  .letE (.var 0) <| .letE (.var 3) <| .letE (.var 5) <| .letE (.var 7) <| .letE (.var 9) <|
  .letE (.var 6) <| .letE (.var 12) <| .letE (.var 14) <|
  .add (coreE m lt leafNode) (.lit 0)

/-! ### The value -/

/-- A word congruent to a small number, reduced, is not zero exactly when the number is not zero. -/
theorem reduce_iff {W x v : ℕ} (h : (x : ZMod (2 ^ W)) = (v : ZMod (2 ^ W))) (hv : v < 2 ^ W) :
    (x + 0 % 2 ^ W) % 2 ^ W ≠ 0 ↔ v ≠ 0 := by
  rw [Nat.zero_mod, add_zero, Ne, Ne, not_iff_not]
  have h1 : x % 2 ^ W = 0 ↔ (x : ZMod (2 ^ W)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  have h2 : v = 0 ↔ (v : ZMod (2 ^ W)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    constructor
    · rintro rfl
      exact dvd_zero _
    · intro hd
      exact Nat.eq_zero_of_dvd_of_lt hd hv
  rw [h1, h2, h]

/-- The bound on the final integer. -/
theorem den_lt {W M Q D n Z K A : ℕ} (hD : 0 < D) (hK : K ≤ 2 * A) (hZ : Z ≤ 2 ^ n)
    (h : Q * (M * M) + 2 * D * A + n < W) :
    M.factorial ^ Q * D ^ K * Z < 2 ^ W := by
  have h1 : M.factorial ≤ 2 ^ (M * M) := by
    calc M.factorial ≤ M ^ M := Nat.factorial_le_pow _
      _ ≤ (2 ^ M) ^ M := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2 ^ (M * M) := (pow_mul _ _ _).symm
  have h2 : D ^ K ≤ 2 ^ (2 * D * A) := by
    calc D ^ K ≤ D ^ (2 * A) := Nat.pow_le_pow_right hD hK
      _ ≤ (2 ^ D) ^ (2 * A) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2 ^ (D * (2 * A)) := (pow_mul _ _ _).symm
      _ = 2 ^ (2 * D * A) := by congr 1; ring
  calc M.factorial ^ Q * D ^ K * Z ≤ (2 ^ (M * M)) ^ Q * 2 ^ (2 * D * A) * 2 ^ n :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h1 _) h2) hZ
    _ = 2 ^ (Q * (M * M) + 2 * D * A + n) := by
        rw [← pow_mul, pow_add, pow_add]
        ring_nf
    _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) h

/-- The sizes for the number of layers. -/
theorem hE_small {W n D a : ℕ} (hD : 1 ≤ D) (ha : 26 * D ≤ a) (h : a * (n + 1) ^ 3 ≤ W) :
    6 * ((n + 1) * D) + 3 < 2 ^ W := by
  have h1 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h2 : 1 ≤ (n + 1) * D := Nat.mul_pos (by omega) hD
  have h3 : 26 * D * (n + 1) ≤ a * (n + 1) ^ 3 := Nat.mul_le_mul ha h1
  have e : 26 * D * (n + 1) = 26 * ((n + 1) * D) := by ring
  have h4 : 6 * ((n + 1) * D) + 3 ≤ W := by omega
  exact lt_of_le_of_lt h4 Nat.lt_two_pow_self

/-! ### The cost -/

theorem layCost_le {M Y : ℕ} (hY : M + 1 ≤ Y) : layCost M ≤ 200 * Y ^ 6 := by
  have hY1 : 1 ≤ Y := by omega
  have h2 : Y ^ 2 ≤ Y ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
  have h3 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) Y
  have h1 : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ hY1
  have h4 : M * (48 + 143 * M) ≤ Y * (48 + 143 * Y) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : Y * (48 + 143 * Y) = 48 * Y + 143 * Y ^ 2 := by ring
  have e2 : layCost M = 2 + M * (48 + 143 * M) := by
    unfold layCost layOne layBody wireWordCost
    ring
  omega

theorem overhead_le {o x c A3 A6 Y6 GK GK' LC : ℕ}
    (h : o ≤ 1 + 1080 * A3 + (1 + 80 * A3 + (1 + 5 + (1 + 30000 * A6 + (1 + 30000 * A6 + (1 + GK + (1 + 15 + (1 + LC +
      (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + x))))))))))))))))
    (hx : x = 1 + c + 1) (h3 : A3 ≤ Y6) (h6 : A6 ≤ Y6) (h1 : 1 ≤ Y6) (hL : LC ≤ 200 * Y6) (hG : GK ≤ GK') :
    o ≤ (100000 * Y6 + 4 * GK') + c := by
  omega

/-- The bound `Y` on the sizes at a leaf. -/
def leafY (K d n : ℕ) : ℕ := (K + 17 * (1 + d) + 3) * (n + 1)

/-! ### The sizes -/

section Sizes

variable {K hl M v fw n D W : ℕ}

theorem hl_le (hK : 0 < K) (hsq : K ^ 2 * hl ≤ 13 * D * n) : hl ≤ 13 * (D * n) := by
  have h1 : hl ≤ K ^ 2 * hl := Nat.le_mul_of_pos_left _ (pow_pos hK _)
  have e : 13 * D * n = 13 * (D * n) := by ring
  omega

/-- The size of the tables, for `big_of_le`. -/
theorem big_size {C : ℕ} (hna : n ≤ D * n) (hma : M ≤ D * n) (hla : hl ≤ 13 * (D * n)) (hv : v ≤ M + n + 1)
    (hfw : fw = K + 3 + M + v) (hW : C * (2 * K + 20 * D + 8) ^ 3 * (n + 1) ^ 3 ≤ W) :
    C * (K + hl + 2 * M + v + fw + 3) ^ 3 ≤ W := by
  refine le_trans ?_ hW
  have e : (2 * K + 20 * D + 8) * (n + 1) = 2 * (K * n) + 20 * (D * n) + 8 * n + 2 * K + 20 * D + 8 := by ring
  have h1 : K + hl + 2 * M + v + fw + 3 ≤ (2 * K + 20 * D + 8) * (n + 1) := by
    rw [e]
    omega
  calc C * (K + hl + 2 * M + v + fw + 3) ^ 3
      ≤ C * ((2 * K + 20 * D + 8) * (n + 1)) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = _ := by ring

theorem num_le {m : ℕ} (hsq : K ^ 2 * hl ≤ 13 * D * n) (hmD : 26 * D ≤ m) (hm1 : n ≤ M) :
    2 * (K ^ 2 * hl) ≤ m * M := by
  have h1 : 26 * D * n ≤ m * n := Nat.mul_le_mul_right _ hmD
  have h2 : m * n ≤ m * M := Nat.mul_le_mul_left _ hm1
  have e : 26 * D * n = 2 * (13 * D * n) := by ring
  omega

/-- The bound `Y` bounds the sizes. -/
theorem leafY_bounds {d : ℕ} (hd : D = 1 + d) (hna : n ≤ D * n) (hma : M ≤ D * n) (hla : hl ≤ 13 * (D * n))
    (hv : v ≤ M + n + 1) :
    n + 1 ≤ leafY K d n ∧ M + 1 ≤ leafY K d n ∧ K + hl + 2 * M + v + 1 ≤ leafY K d n ∧ v + 1 ≤ leafY K d n ∧
      M + v + 1 ≤ leafY K d n ∧ 1 ≤ leafY K d n := by
  have hYe : leafY K d n = K * n + K + 17 * (D * n) + 17 * D + 3 * n + 3 := by
    subst hd
    simp only [leafY]
    ring
  rw [hYe]
  omega

/-- The bound on the exponent of the final integer. -/
theorem small_le {q d0 : ℕ} (hma : M ≤ D * n)
    (hW : (q * D ^ 2 + 26 * d0 * D + 2) * (n + 1) ^ 3 ≤ W) :
    q * (M * M) + 2 * d0 * (13 * (D * n)) + n < W := by
  set A := n + 1 with hA
  have hA3 : 1 ≤ A ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hMA : M ≤ D * A := by
    have : D * A = D * n + D := by
      rw [hA]
      ring
    omega
  have s1 : M * M ≤ D ^ 2 * A ^ 3 := by
    calc M * M ≤ (D * A) * (D * A) := Nat.mul_le_mul hMA hMA
      _ = D ^ 2 * A ^ 2 := by ring
      _ ≤ D ^ 2 * A ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have s2 : D * n ≤ D * A ^ 3 := by
    have h1 : D * n ≤ D * A := Nat.mul_le_mul_left _ (by omega)
    have h2 : D * A ≤ D * A ^ 3 := Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
    omega
  have s3 : n + 1 ≤ A ^ 3 := Nat.le_self_pow (by norm_num) _
  have e : (q * D ^ 2 + 26 * d0 * D + 2) * A ^ 3 =
      q * (D ^ 2 * A ^ 3) + 26 * d0 * (D * A ^ 3) + 2 * A ^ 3 := by ring
  have s4 := Nat.mul_le_mul_left q s1
  have s5 := Nat.mul_le_mul_left (26 * d0) s2
  have e2 : 2 * d0 * (13 * (D * n)) = 26 * d0 * (D * n) := by ring
  omega

/-- The sizes for the number of layers, from the size of the final integer. -/
theorem hE_small' {q d0 : ℕ} (hD : 1 ≤ D) (hd0 : 0 < d0) (hW : (q * D ^ 2 + 26 * d0 * D + 2) * (n + 1) ^ 3 ≤ W) :
    6 * ((n + 1) * D) + 3 < 2 ^ W := by
  refine hE_small (a := q * D ^ 2 + 26 * d0 * D + 2) hD ?_ hW
  have : 26 * D * 1 ≤ 26 * D * d0 := Nat.mul_le_mul_left _ hd0
  have e : 26 * d0 * D = 26 * D * d0 := by ring
  omega

end Sizes

/-! ### The leaf -/

/-- **One leaf.** Here `G` is the formula of the leaf, with at most `d` occurrences of each variable and at least `K ^ 2` variables, and the word
size `W` satisfies the three displayed bounds. The value is not zero exactly when `G` is satisfiable. The cost is the cost of the tables and the
placement, and the cost of the core program. -/
theorem leaf_main {m Kc dc : ℕ}
    (hKd : ∀ S : Setup, S.m = m → ops S.W (coreE S.m S.lt S.nodeE) S.core ≤
      S.Q * S.Nq ^ S.Q * S.nS ^ 3 *
        (Kc * S.T ^ dc +
          S.L * 2 ^ (S.M / S.m) * (Kc * S.T ^ dc + 2 * (S.Unode * (S.v + 1)))))
    {W n d : ℕ} {lt : Lits} (hlt : lt.Good m) (h40 : 40 ≤ m) (hmD : 26 * (1 + d) ≤ m)
    {G : ClauseSet (SignedLiteral n)} (hF : Wide3 G) (hd3 : 3 ≤ d) (hdeg : ∀ v, variableOccurrences G v ≤ d)
    (hth : Kof m ^ 2 ≤ n)
    (hW1 : (48 + (2 * d + Kof m + 12) ^ 2) * (n + 1) ^ 3 ≤ W)
    (hW2 : wConst m lt * (2 * Kof m + 20 * (1 + d) + 8) ^ 3 * (n + 1) ^ 3 ≤ W)
    (hW3 : (m ^ 4 * (1 + d) ^ 2 + 26 * lt.D * (1 + d) + 2) * (n + 1) ^ 3 ≤ W)
    (p root enc : ℕ) (rest : List ℕ) :
    (eval W (leafE m d lt) (encF n G :: p :: root :: enc :: n :: rest) ≠ 0 ↔
      ∃ x, holdsFormula (literalHolds x) G) ∧
    (ops W (leafE m d lt) (encF n G :: p :: root :: enc :: n :: rest) : ℝ) ≤
      ((100000 * leafY (Kof m) d n ^ 6 + 4 * (greedyK (m ^ 4) (Kof m) * leafY (Kof m) d n ^ 3) : ℕ) : ℝ) +
        (6 * (m : ℝ)) ^ 9 * Real.exp (9 * (Real.log m + 3) * ((4 * (1 + d) * n : ℕ) : ℝ) / m) *
          (((m ^ 4 : ℕ) : ℝ) * (Kc + ((6 * m ^ 4 : ℕ) : ℝ) * (Kc + 68000))) *
            (leafY (Kof m) d n : ℝ) ^ (m ^ 4 + dc + 7) := by
  classical
  have hm0 : 0 < m := by omega
  have hQ0 : 0 < m ^ 4 := by positivity
  have hL2 : 2 ≤ 6 * m ^ 4 := by omega
  have hL0 : 0 < 6 * m ^ 4 := by omega
  have hKpos : 0 < Kof m := pow_pos hL0 _
  have hDlt : 0 < lt.D := hlt.D_pos
  set E0 : List ℕ := encF n G :: p :: root :: enc :: n :: rest with hE0
  set M := mN n G with hMdef
  set v := vN n G with hvdef
  set fw := fwN (Kof m) M v with hfw
  have cn := fun (E : List ℕ) (nv fv : ℕ) (h1 : E.getD nv 0 = n) (h2 : E.getD fv 0 = encF n G) =>
    cnf_net_main (env := E) (nv := nv) (fv := fv) hF (K := Kof m) hd3 hdeg hKpos hW1 h1 h2
  obtain ⟨rm, -, hm1, hm2, hv1, -, hB, -, harity, hNet, -, -, -, hcount, hnode⟩ := cn E0 4 0 rfl rfl
  obtain ⟨-, rv, -⟩ := cn (M :: E0) 5 1 rfl rfl
  have rf : CnfTree.Run W (fwE (Kof m) 1 0) (v :: M :: E0) fw 5 :=
    run_fwE hfw hB rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ht, -⟩ := cn (fw :: v :: M :: E0) 7 3 rfl rfl
  have rt := (ht (ifw := 0) rfl).1
  set tT := tailTN n G fw with htT
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := cn (tT :: fw :: v :: M :: E0) 8 4 rfl rfl
  have rh := (hh (ifw := 1) rfl).2
  set hT := headTN n G fw with hhT
  set env5 : List ℕ := hT :: tT :: fw :: v :: M :: E0 with henv5
  -- the placement
  have hShape := shape_net hF harity
  have hK2 : Kof m ≤ 2 ^ fw := hB.K_lt.le
  have hKW : Kof m < 2 ^ W := hB.lit_K
  have hQK : m ^ 4 < Kof m := GreedySpec.Q_lt_pow hL2
  have hLK : 6 * m ^ 4 ≤ Kof m := by
    calc 6 * m ^ 4 = (6 * m ^ 4) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right hL0 hQ0
  have hQW : m ^ 4 < 2 ^ W := by omega
  have hLW : 6 * m ^ 4 < 2 ^ W := by omega
  set R := Greedy.table fw n (m ^ 4) (6 * m ^ 4) (tailN hF) (headN hF) v with hR
  have r1 : CnfTree.Run W (greedyE (m ^ 4) (6 * m ^ 4) 9 4 3 2 1 0) env5 R (greedyK (m ^ 4) (Kof m) * (M + v + 1) ^ 3) :=
    greedy_spec hB hL2 hNet hQW hLW rfl rfl rfl rfl rfl rfl
  -- the layers
  set hl := Greedy.capB n (Kof m) (1 + d) with hhl
  have r2 : CnfTree.Run W (hE (Kof m) (1 + d) 10) (R :: env5) hl 15 :=
    GreedySpec.run_hE rfl (Nat.le_add_right 1 d) hKW (hE_small' (Nat.le_add_right 1 d) hDlt hW3)
  set lT := GreedySpec.layTable fw R (tailN hF) (headN hF) with hlT
  have r3 : CnfTree.Run W (layTE 6 3 2 4 1) (hl :: R :: env5) lT (layCost M) :=
    GreedySpec.run_layTE hB hNet rfl rfl rfl rfl rfl
  set outer : List ℕ := lT :: hl :: R :: env5 with houter
  -- the sizes
  have hna : n ≤ (1 + d) * n := Nat.le_mul_of_pos_left _ (by omega)
  have hsq : Kof m ^ 2 * hl ≤ 13 * (1 + d) * n := Greedy.sq_mul_capB_le hth (by omega)
  have hla : hl ≤ 13 * ((1 + d) * n) := hl_le hKpos hsq
  have hbig : Big m hl M v fw W lt := big_of_le (big_size hna hm2 hla hv1 rfl hW2)
  have hnum : 2 * (Kof m ^ 2 * hl) ≤ m * M := num_le hsq hmD hm1
  obtain ⟨hYn, hYM, hYT, hYv, hYMv, hY1⟩ := leafY_bounds (K := Kof m) rfl hna hm2 hla hv1
  let S : Setup :=
    { m := m, M := M, v := v, h := hl, fw := fw, W := W, hm := h40, lt := lt, hlt := hlt
      tail := tailN hF, head := headN hF
      wd := Greedy.wdOf hL0 fw R
      wi := Greedy.wiresOf hShape rfl hQ0 hK2
      hOn := Greedy.onNodes_wiresOf hShape rfl hQ0 hK2
      hnum := hnum
      tailT := tT, headT := hT, partT := R, layT := lT, outer := outer
      htail := hNet.tail_eq, hhead := hNet.head_eq
      hpart := fun α => (Code.wordIdx_wordOf hL0 (Greedy.fld_table_lt hKpos hK2 α.2)).symm
      hlay := fun e => GreedySpec.fld_layTable hB R e
      φ := fun α g => phiN hF α g
      nodeE := leafNode, Unode := 34000 * (n + 1) ^ 6
      hnode := fun α A _ => by
        obtain ⟨b, hb, he⟩ := hnode hl tT hT (R :: lT :: outer) hNet α A 22 18 rfl rfl
        exact (TransposeBase.Pseudo.Leaf.Run.toZ hb).eq he
      big := hbig }
  -- the cost of the core program
  have hcore := core_real hKd S rfl (Y := leafY (Kof m) d n) hY1 hYM hYT hYv
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hYn _))
  -- the whole run
  set Cc := coreE m lt leafNode with hCc
  have rC : CnfTree.Run W (.add Cc (.lit 0)) S.core (eval W (.add Cc (.lit 0)) S.core)
      (ops W (.add Cc (.lit 0)) S.core) := ⟨rfl, le_rfl⟩
  have hrun := run_let rm <| run_let rv <| run_let rf <| run_let rt <| run_let rh <| run_let r1 <| run_let r2 <|
    run_let r3 <|
    run_let (run_var (i := 0) (v := lT) rfl) <| run_let (run_var (i := 3) (v := R) rfl) <|
    run_let (run_var (i := 5) (v := hT) rfl) <| run_let (run_var (i := 7) (v := tT) rfl) <|
    run_let (run_var (i := 9) (v := fw) rfl) <| run_let (run_var (i := 6) (v := hl) rfl) <|
    run_let (run_var (i := 12) (v := v) rfl) <| run_let (run_var (i := 14) (v := M) rfl) rC
  have hrunV : eval W (leafE m d lt) E0 = eval W (.add Cc (.lit 0)) S.core := hrun.1
  have hrunO : ops W (leafE m d lt) E0 ≤ _ := hrun.2
  have hopsAdd : ops W (.add Cc (.lit 0)) S.core = 1 + ops W Cc S.core + 1 := rfl
  -- the value
  have hval := coreE_eval S
  have hsum : ∑ z : Fin S.M → Bool, ∏ α, S.φ α (fun e => z e.1) =
      ((univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) G).card : ℤ) := hcount
  rw [hsum] at hval
  have hZle : (univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) G).card ≤ 2 ^ n := by
    refine (card_le_univ _).trans ?_
    simp
  have hZiff : (univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) G).card ≠ 0 ↔
      ∃ x, holdsFormula (literalHolds x) G := by
    rw [Finset.card_ne_zero, Finset.filter_nonempty_iff]
    simp
  generalize (univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) G).card = Z at hval hZle hZiff
  have hkeys : 2 * S.nKeys ≤ 2 * (13 * ((1 + d) * n)) :=
    Nat.mul_le_mul_left _ ((S.card_keys_le.trans hsq).trans (le_of_eq (by ring)))
  generalize hK2' : 2 * S.nKeys = K2 at hval hkeys
  have hval2 : ((eval W Cc S.core : ℕ) : ZMod (2 ^ W)) =
      ((M.factorial ^ (m ^ 4) * lt.D ^ K2 * Z : ℕ) : ZMod (2 ^ W)) := by
    have e : ((eval W Cc S.core : ℕ) : ZMod (2 ^ W)) =
        ((((M.factorial ^ (m ^ 4) * lt.D ^ K2 : ℕ) : ℤ) * (Z : ℤ) : ℤ) : ZMod (2 ^ W)) := hval
    rw [e]
    push_cast
    rfl
  have hvlt : M.factorial ^ (m ^ 4) * lt.D ^ K2 * Z < 2 ^ W :=
    den_lt hDlt hkeys hZle (small_le hm2 hW3)
  have hred : eval W (.add Cc (.lit 0)) S.core ≠ 0 ↔ M.factorial ^ (m ^ 4) * lt.D ^ K2 * Z ≠ 0 :=
    reduce_iff hval2 hvlt
  refine ⟨?_, ?_⟩
  · rw [hrunV, hred, ← hZiff]
    have h1 : M.factorial ^ (m ^ 4) ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero _)
    have h2 : lt.D ^ K2 ≠ 0 := pow_ne_zero _ hDlt.ne'
    rw [Nat.mul_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨mul_ne_zero h1 h2, h⟩⟩
  · -- the cost
    have hcore' : (ops W Cc S.core : ℝ) ≤ (6 * (m : ℝ)) ^ 9 * Real.exp (9 * (Real.log m + 3) * (M : ℝ) / m) *
        (((m ^ 4 : ℕ) : ℝ) * (Kc + ((6 * m ^ 4 : ℕ) : ℝ) * (Kc + 68000))) *
          (leafY (Kof m) d n : ℝ) ^ (m ^ 4 + dc + 7) := hcore
    have hNr : (M : ℝ) ≤ ((4 * (1 + d) * n : ℕ) : ℝ) := by
      have : M ≤ 4 * (1 + d) * n := by
        calc M ≤ (1 + d) * n := hm2
          _ ≤ 4 * ((1 + d) * n) := Nat.le_mul_of_pos_left _ (by norm_num)
          _ = 4 * (1 + d) * n := by ring
      exact_mod_cast this
    have hm0r : (0 : ℝ) < m := by exact_mod_cast hm0
    have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg _
    have hexp : Real.exp (9 * (Real.log m + 3) * (M : ℝ) / m) ≤
        Real.exp (9 * (Real.log m + 3) * ((4 * (1 + d) * n : ℕ) : ℝ) / m) :=
      exp_mono hlog0 hm0r hNr
    have hA3Y : (n + 1) ^ 3 ≤ leafY (Kof m) d n ^ 6 :=
      (Nat.pow_le_pow_right (by omega) (by norm_num)).trans (Nat.pow_le_pow_left hYn 6)
    have hA6Y : (n + 1) ^ 6 ≤ leafY (Kof m) d n ^ 6 := Nat.pow_le_pow_left hYn 6
    have hY6 : 1 ≤ leafY (Kof m) d n ^ 6 := Nat.one_le_pow _ _ hY1
    have hGK : greedyK (m ^ 4) (Kof m) * (M + v + 1) ^ 3 ≤ greedyK (m ^ 4) (Kof m) * leafY (Kof m) d n ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hYMv _)
    have hLC : layCost M ≤ 200 * leafY (Kof m) d n ^ 6 := layCost_le hYM
    have hnat : ops W (leafE m d lt) E0 ≤
        (100000 * leafY (Kof m) d n ^ 6 + 4 * (greedyK (m ^ 4) (Kof m) * leafY (Kof m) d n ^ 3)) + ops W Cc S.core :=
      overhead_le hrunO hopsAdd hA3Y hA6Y hY6 hLC hGK
    have hq : (0 : ℝ) ≤ ((m ^ 4 : ℕ) : ℝ) * (Kc + ((6 * m ^ 4 : ℕ) : ℝ) * (Kc + 68000)) :=
      mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _) (by norm_num))))
    exact cost_real hnat hcore' hexp (by positivity) hq
      (pow_nonneg (Nat.cast_nonneg _) _)

end OnePigeonhole.Pseudo.Final
