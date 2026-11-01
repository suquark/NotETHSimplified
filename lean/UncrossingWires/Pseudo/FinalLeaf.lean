import UncrossingWires.Pseudo.CoreSpec
import UncrossingWires.Pseudo.GreedySpec
import TransposeBase.Pseudo.CnfNet

/-!
# The program for one leaf of the branching tree

`leafE L H` runs on `encF n G :: p :: root :: enc :: n :: rest`. It computes the network of `G`, its greedy placement into
`Ktow L H` words, and then it runs the core program. The value is not zero exactly when `G` is satisfiable (`leaf_main`).

`psi_part` is the bound on the potential of the first level, for `Ktow L H ^ 2 ≤ n`: the greedy placement puts few wires
between two words, so the weights are small, and the square of a weight is at most the weight times its bound.
-/

namespace UncrossingWires.Pseudo.Final

open Finset TransposeBase TransposeBase.General TransposeBase.Pseudo
  TransposeBase.Pseudo.Code TransposeBase.Pseudo.Leaf SatBase TransposeBase.Pseudo.CnfTree
  TransposeBase.Pseudo.CnfNet TransposeBase.Pseudo.Place TransposeBase.Sat

/-! ### The parameters -/

/-- The number of words at height `h`, as a power of `L`. -/
theorem Ktow_eq (L h : ℕ) : Ktow L h = L ^ 2 ^ h := by
  induction h with
  | zero => simp [Ktow]
  | succ h ih =>
    rw [Ktow, ih, ← pow_add, pow_succ 2 h, mul_two]

/-- The number of rectangles of a chain. The power of two of a chain is the scale times this number. -/
def nRectTot (L H : ℕ) : ℕ := scaleTot L 1 H

theorem scaleTot_eq (L sc H : ℕ) : scaleTot L sc H = sc * nRectTot L H := by
  induction H with
  | zero => simp [nRectTot, scaleTot]
  | succ H ih =>
    simp only [nRectTot, scaleTot] at ih ⊢
    rw [ih]
    ring

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

/-- The network of a formula has the shape of the greedy placement. -/
theorem shape_net (hF : Wide3 F) {D : ℕ} (harity : ∀ α, Spread.arity (tailN hF) (headN hF) α ≤ D) :
    Greedy.Shape n D (tailN hF) (headN hF) where
  tail_lt := tailN_lt hF
  le_head := le_headN hF
  card_tail a := (card_le_card fun _ he =>
    mem_filter.mpr ⟨mem_univ _, Or.inl (mem_filter.mp he).2⟩).trans (harity a)
  card_head := card_headN_le hF

end Shape

/-! ### The potential of the first level -/

/-- The bound on the potential of the first level, at a leaf. -/
def leafP (d n : ℕ) : ℕ := 28 * ((1 + d) * n) ^ 2

/-- **The potential of the first level.** The greedy table has few wires between two words. -/
theorem psi_part {K m v fw n d : ℕ} {N : BaseNet m v} (S : Greedy.Shape n (1 + d) N.tail N.head) (hK : 0 < K)
    (hK2 : K ≤ 2 ^ fw) (hr : ∀ α, N.rOf α = fld fw (Greedy.table fw n K N.tail N.head v) α) (hth : K ^ 2 ≤ n)
    (hd3 : 3 ≤ d) (hm : m ≤ (1 + d) * n) :
    K ^ 2 * psi K N.w0 ≤ leafP d n :=
  Greedy.psi_table_le S hK hK2 hr hth (by omega) hm

/-! ### The sizes -/

theorem bits_lt {X D n m W : ℕ} (hm : m ≤ D * n) (h : (X + 16 * D + 9) * (n + 1) ^ 3 ≤ W) :
    X + 8 * (2 * m) + 8 < W := by
  have hA1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hAn : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hmA : D * n ≤ D * (n + 1) ^ 3 := Nat.mul_le_mul_left _ (by omega)
  have hX : X ≤ X * (n + 1) ^ 3 := Nat.le_mul_of_pos_right _ hA1
  have e : (X + 16 * D + 9) * (n + 1) ^ 3 = X * (n + 1) ^ 3 + 16 * (D * (n + 1) ^ 3) + 9 * (n + 1) ^ 3 := by ring
  omega

theorem cube_lt {D n m W : ℕ} (hm : m ≤ D * n) (h : ((2 * D + 2) ^ 3 + 1) * (n + 1) ^ 3 ≤ W) :
    (2 * m + 2) ^ 3 < W := by
  have hA1 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h1 : 2 * m + 2 ≤ (2 * D + 2) * (n + 1) := by
    have e : (2 * D + 2) * (n + 1) = 2 * (D * n) + 2 * D + 2 * n + 2 := by ring
    omega
  have h2 : (2 * m + 2) ^ 3 ≤ (2 * D + 2) ^ 3 * (n + 1) ^ 3 := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left h1 3
  have e : ((2 * D + 2) ^ 3 + 1) * (n + 1) ^ 3 = (2 * D + 2) ^ 3 * (n + 1) ^ 3 + (n + 1) ^ 3 := by ring
  omega

theorem scale_lt {D T n m W : ℕ} (hm : m ≤ D * n) (h : (2 * D * T + 1) * (n + 1) ^ 3 ≤ W) :
    2 * m * T + n < W := by
  have hAn : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h1 : 2 * m * T ≤ 2 * D * T * (n + 1) := by
    calc 2 * m * T ≤ 2 * (D * n) * T := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)
      _ = 2 * D * T * n := by ring
      _ ≤ 2 * D * T * (n + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (2 * D * T + 1) * (n + 1) ≤ (2 * D * T + 1) * (n + 1) ^ 3 := Nat.mul_le_mul_left _ hAn
  have e : (2 * D * T + 1) * (n + 1) = 2 * D * T * (n + 1) + (n + 1) := by ring
  omega

/-- The sizes of the fields of binomials. -/
theorem sizes_of {W sc : ℕ} (h : (sc + 2) ^ 3 < W) : Lag.Sizes W sc ((sc + 2) * (sc + 2)) := by
  have hfac : (sc + 1).factorial < 2 ^ ((sc + 2) * (sc + 2)) := by
    calc (sc + 1).factorial ≤ (sc + 1) ^ (sc + 1) := Nat.factorial_le_pow _
      _ ≤ (2 ^ (sc + 1)) ^ (sc + 1) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2 ^ ((sc + 1) * (sc + 1)) := (pow_mul _ _ _).symm
      _ < 2 ^ ((sc + 2) * (sc + 2)) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  refine ⟨hfac, by nlinarith, ?_, by nlinarith⟩
  calc (sc + 2) * (sc + 2) * (sc + 2) = (sc + 2) ^ 3 := by ring
    _ < W := h

/-! ### The value -/

/-- A sum over a range is below `2 ^ W`. -/
theorem eval_sum_lt (W : ℕ) (a b : Expr) (env : List ℕ) : eval W (.sum a b) env < 2 ^ W := by
  rw [TransposeBase.Pseudo.eval_sum]
  exact Nat.mod_lt _ (by positivity)

/-- A word congruent to `2 ^ s * Z`, with `2 ^ s * Z` below `2 ^ W`, is not zero exactly when `Z` is not zero. -/
theorem value_iff {W x s n Z : ℕ} (hx : x < 2 ^ W)
    (hval : (x : ZMod (2 ^ W)) = ((2 ^ s * (Z : ℤ) : ℤ) : ZMod (2 ^ W))) (hZ : Z ≤ 2 ^ n) (hs : s + n < W) :
    x ≠ 0 ↔ Z ≠ 0 := by
  have hlt : 2 ^ s * Z < 2 ^ W := by
    calc 2 ^ s * Z ≤ 2 ^ s * 2 ^ n := Nat.mul_le_mul_left _ hZ
      _ = 2 ^ (s + n) := (pow_add _ _ _).symm
      _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hs
  have h1 : (x : ZMod (2 ^ W)) = ((2 ^ s * Z : ℕ) : ZMod (2 ^ W)) := by
    rw [hval]
    push_cast
    rfl
  have h2 : x = 2 ^ s * Z := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hlt] at this
  rw [h2]
  have h3 : 2 ^ s ≠ 0 := by positivity
  rw [Nat.mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨h3, h⟩⟩

/-! ### The leaf -/

/-- The bound on the sizes at a leaf. -/
def leafY (d n : ℕ) : ℕ := (2 * (1 + d) + 2) * (n + 1)

/-- The cost constant of a leaf, for `K` words and the constant `A` of the core program. -/
def leafC (K d A : ℕ) : ℕ := (100000 + greedyK K + 34001 * A) * (2 * (1 + d) + 2) ^ 9

/-- The node program of the core program. -/
def leafNodeG : ℕ → Expr := fun g => CnfNet.nodeE (g + 13) (g + 9)

theorem cost_le {o A3 A6 PK Y core : ℕ}
    (h : o ≤ 1 + 1080 * A3 + (1 + 80 * A3 + (1 + 5 + (1 + 30000 * A6 + (1 + 30000 * A6 + (1 + PK + (1 + (1 + 1 + 1) +
      (1 + (1 + (1 + 1 + 1) + (1 + 1 + 1)) + core))))))))
    (h3 : A3 ≤ Y) (h6 : A6 ≤ Y) (h1 : 1 ≤ Y) :
    o ≤ 100000 * Y + PK + core := by
  omega

/-- **One leaf.** Here `G` is the formula of the leaf, with at most `d` occurrences of each variable, on `n ≥ K ^ 2` variables
for `K = Ktow L H`, and the word size `W` satisfies the displayed bounds. The value is not zero exactly when `G` is satisfiable.
The cost is a polynomial in `n` times the exponential of the ends of the chain. `A` is the constant of `core_spec`. -/
theorem leaf_main {A L H : ℕ}
    (hA : ∀ {W m v Unode P : ℕ} {f : Frm} {N : BaseNet m v} {nodeG : ℕ → Expr},
      CoreOK W f L H N nodeG Unode P →
      RunZ W (coreE L H nodeG) f.list.tail
        (2 ^ scaleTot L (2 * m) H * ∑ z : Fin m → Bool, ∏ α, N.φ α (fun e => z e.1))
        (A * (m + v + 1) ^ 3 * (Unode + 1) * 2 ^ ((∑ i ∈ range H, EbD L H P i) + Ef H P)))
    (hL : 2 ≤ L)
    {W n d : ℕ} {G : ClauseSet (SignedLiteral n)} (hF : Wide3 G) (hd3 : 3 ≤ d)
    (hdeg : ∀ v, variableOccurrences G v ≤ d)
    (hth : Ktow L H ^ 2 ≤ n)
    (hW1 : (48 + (2 * d + Ktow L H + 12) ^ 2) * (n + 1) ^ 3 ≤ W)
    (hW2 : ((Ktow L H + 1) ^ 4 + chainBits L H + 16 * (1 + d) + 9) * (n + 1) ^ 3 ≤ W)
    (hW3 : ((2 * (1 + d) + 2) ^ 3 + 1) * (n + 1) ^ 3 ≤ W)
    (hW4 : (2 * (1 + d) * nRectTot L H + 1) * (n + 1) ^ 3 ≤ W)
    (p root enc : ℕ) (rest : List ℕ) :
    (eval W (leafE L H) (encF n G :: p :: root :: enc :: n :: rest) ≠ 0 ↔
      ∃ x, holdsFormula (literalHolds x) G) ∧
    ops W (leafE L H) (encF n G :: p :: root :: enc :: n :: rest) ≤
      leafC (Ktow L H) d A * (n + 1) ^ 9 *
        2 ^ ((∑ i ∈ range H, EbD L H (leafP d n) i) + Ef H (leafP d n)) := by
  classical
  have hLpos : 0 < L := by omega
  set E0 : List ℕ := encF n G :: p :: root :: enc :: n :: rest with hE0
  set K := Ktow L H with hK
  have hKpos : 0 < K := Ktow_pos hLpos H
  set m := mN n G with hm
  set v := vN n G with hv
  set fw := fwN K m v with hfw
  have M := fun (E : List ℕ) (nv fv : ℕ) (h1 : E.getD nv 0 = n) (h2 : E.getD fv 0 = encF n G) =>
    cnf_net_main (env := E) (nv := nv) (fv := fv) hF (K := K) hd3 hdeg hKpos hW1 h1 h2
  obtain ⟨rm, -, hm1, hm2, hv1, -, hB, -, harity, hNet, -, -, -, hcount, hnode⟩ :=
    M E0 4 0 rfl rfl
  obtain ⟨-, rv, -⟩ := M (m :: E0) 5 1 rfl rfl
  have rf : CnfTree.Run W (fwE K 1 0) (v :: m :: E0) fw 5 :=
    run_fwE hfw hB rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ht, -⟩ := M (fw :: v :: m :: E0) 7 3 rfl rfl
  have rt := (ht (ifw := 0) rfl).1
  set tT := tailTN n G fw with htT
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := M (tT :: fw :: v :: m :: E0) 8 4 rfl rfl
  have rh := (hh (ifw := 1) rfl).2
  set hT := headTN n G fw with hhT
  set env5 : List ℕ := hT :: tT :: fw :: v :: m :: E0 with henv5
  -- the placement
  set R := Greedy.table fw n K (tailN hF) (headN hF) v with hR
  have r1 : CnfTree.Run W (greedyE K 9 4 3 2 1 0) env5 R (greedyK K * (m + v + 1) ^ 3) :=
    greedy_spec hB hNet rfl rfl rfl rfl rfl rfl
  have hK2 : K ≤ 2 ^ fw := hB.K_lt.le
  -- the sizes
  have hmD : m ≤ (1 + d) * n := hm2
  have hbits : (K + 1) ^ 4 + chainBits L H + 8 * (2 * m) + 8 < W := bits_lt hmD hW2
  have hcube : (2 * m + 2) ^ 3 < W := cube_lt hmD hW3
  have hscale : 2 * m * nRectTot L H + n < W := scale_lt hmD hW4
  have hsizes := sizes_of hcube
  -- the network and the frame
  let N : BaseNet m v :=
    { tail := tailN hF, head := headN hF, rOf := fun α => fld fw R α, φ := fun α g => phiN hF α g }
  have hrK : ∀ α, N.rOf α < Ktow L H := fun α => Greedy.fld_table_lt hKpos hK2 α.2
  let f : Frm :=
    { c := 0, bk := (2 * m + 2) * (2 * m + 2), sc := 2 * m, pT := R, hT := hT, tT := tT, fw := fw, v := v, m := m,
      rest := E0 }
  have hCore : CoreOK W f L H N leafNodeG (34000 * (n + 1) ^ 6) (leafP d n) := by
    refine ⟨hL, fun c0 => ⟨rfl, rfl, hNet.tail_eq, hNet.head_eq, fun _ => rfl, hrK, hKpos, hB, rfl, ?_, ?_⟩,
      ⟨hsizes, ?_⟩, hbits, ?_⟩
    · show (K + 1) ^ 4 + 8 * (2 * m) + 8 < W
      omega
    · intro g env hAt α A' a1 a2 _
      have g13 : env.getD (g + 13) 0 = n := hAt.getD 13
      have g9 : env.getD (g + 9) 0 = encF n G := hAt.getD 9
      obtain ⟨b, hb, he⟩ := hnode 0 tT hT (a1 :: a2 :: env) hNet α A' (g + 10 + 13) (g + 10 + 9)
        (by simpa [Nat.add_right_comm g 10] using g13) (by simpa [Nat.add_right_comm g 10] using g9)
      exact (Run.toZ hb).eq he
    · show 8 * (2 * m) + 8 < W
      omega
    · exact psi_part (shape_net hF harity) hKpos hK2 (fun _ => rfl) hth hd3 hmD
  have hC := hA hCore
  -- the whole run
  have hA3 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 < 2 ^ W := by
    have h8 : 8 ≤ (2 * m + 2) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (2 * m + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hWpow : W < 2 ^ W := Nat.lt_two_pow_self
  have hsq : (2 * m + 2) * (2 * m + 2) ≤ (2 * m + 2) ^ 3 := by
    rw [pow_succ, sq]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hself : 2 * m + 2 ≤ (2 * m + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hs1 : 2 * m < 2 ^ W := by omega
  have hs2 : 2 * m + 2 < 2 ^ W := by omega
  have rS : CnfTree.Run W (.mul (.lit 2) (.var 5)) (R :: env5) (2 * m) (1 + 1 + 1) :=
    CnfTree.run_mul (CnfTree.run_lit h2) (CnfTree.run_var rfl) hs1
  have rS2 : CnfTree.Run W (.add (.var 0) (.lit 2)) (2 * m :: R :: env5) (2 * m + 2) (1 + 1 + 1) :=
    CnfTree.run_add (CnfTree.run_var rfl) (CnfTree.run_lit h2) hs2
  have rB : CnfTree.Run W (.mul (.add (.var 0) (.lit 2)) (.add (.var 0) (.lit 2))) (2 * m :: R :: env5)
      ((2 * m + 2) * (2 * m + 2)) (1 + (1 + 1 + 1) + (1 + 1 + 1)) :=
    CnfTree.run_mul rS2 rS2 (by omega)
  set envC : List ℕ := (2 * m + 2) * (2 * m + 2) :: 2 * m :: R :: env5 with henvC
  have rC : CnfTree.Run W (coreE L H leafNodeG) envC (eval W (coreE L H leafNodeG) envC)
      (ops W (coreE L H leafNodeG) envC) := ⟨rfl, le_rfl⟩
  have hrun := CnfTree.run_let rm <| CnfTree.run_let rv <| CnfTree.run_let rf <| CnfTree.run_let rt <| CnfTree.run_let rh <| CnfTree.run_let r1 <| CnfTree.run_let rS <|
    CnfTree.run_let rB rC
  have hrunV : eval W (leafE L H) E0 = eval W (coreE L H leafNodeG) envC := hrun.1
  have hrunO : ops W (leafE L H) E0 ≤ _ := hrun.2
  -- the value
  have hval : ((eval W (coreE L H leafNodeG) envC : ℕ) : ZMod (2 ^ W)) =
      ((2 ^ (2 * m * nRectTot L H) * ((univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) G).card : ℤ) : ℤ) :
        ZMod (2 ^ W)) := by
    have e1 : ((eval W (coreE L H leafNodeG) envC : ℕ) : ZMod (2 ^ W)) =
        ((2 ^ scaleTot L (2 * m) H * ∑ z : Fin m → Bool, ∏ α, N.φ α (fun e => z e.1) : ℤ) : ZMod (2 ^ W)) := hC.1
    rw [e1, scaleTot_eq]
    have e2 : ∑ z : Fin m → Bool, ∏ α, N.φ α (fun e => z e.1) =
        ((univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) G).card : ℤ) := hcount
    rw [e2]
  have hZle : (univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) G).card ≤ 2 ^ n := by
    refine (card_le_univ _).trans ?_
    simp
  have hZiff : (univ.filter fun x : Fin n → Bool => holdsFormula (literalHolds x) G).card ≠ 0 ↔
      ∃ x, holdsFormula (literalHolds x) G := by
    rw [Finset.card_ne_zero, Finset.filter_nonempty_iff]
    simp
  refine ⟨?_, ?_⟩
  · have hlt : eval W (coreE L H leafNodeG) envC < 2 ^ W := eval_sum_lt W _ _ envC
    rw [hrunV, value_iff hlt hval hZle hscale, hZiff]
  · -- the cost
    set Z := 2 ^ ((∑ i ∈ range H, EbD L H (leafP d n) i) + Ef H (leafP d n)) with hZ
    have hcore : ops W (coreE L H leafNodeG) envC ≤
        A * (m + v + 1) ^ 3 * (34000 * (n + 1) ^ 6 + 1) * Z := hC.2
    set D := 2 * (1 + d) + 2 with hD
    have hYe : leafY d n = D * (n + 1) := rfl
    set Y := leafY d n with hY
    have hYv : m + v + 1 ≤ Y := by
      have e : D * (n + 1) = 2 * ((1 + d) * n) + 2 * (1 + d) + 2 * n + 2 := by
        rw [hD]
        ring
      rw [hYe, e]
      omega
    have hYn : n + 1 ≤ Y := by
      rw [hYe]
      exact Nat.le_mul_of_pos_left _ (by omega)
    have hY1 : 1 ≤ Y := by omega
    have hY3 : (n + 1) ^ 3 ≤ Y ^ 9 :=
      (Nat.pow_le_pow_left hYn 3).trans (Nat.pow_le_pow_right hY1 (by norm_num))
    have hY6 : (n + 1) ^ 6 ≤ Y ^ 9 :=
      (Nat.pow_le_pow_left hYn 6).trans (Nat.pow_le_pow_right hY1 (by norm_num))
    have hY91 : 1 ≤ Y ^ 9 := Nat.one_le_pow _ _ hY1
    have hZpos : 1 ≤ Z := Nat.one_le_two_pow
    have s1 : ops W (leafE L H) E0 ≤ 100000 * Y ^ 9 + greedyK K * (m + v + 1) ^ 3 + ops W (coreE L H leafNodeG) envC :=
      cost_le hrunO hY3 hY6 hY91
    have s2 : greedyK K * (m + v + 1) ^ 3 ≤ greedyK K * Y ^ 9 :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hYv 3).trans (Nat.pow_le_pow_right hY1 (by norm_num)))
    have s3 : A * (m + v + 1) ^ 3 * (34000 * (n + 1) ^ 6 + 1) * Z ≤
        A * Y ^ 3 * (34001 * Y ^ 6) * Z := by
      refine Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hYv 3)) ?_) le_rfl
      have : (n + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hYn 6
      have : 1 ≤ Y ^ 6 := Nat.one_le_pow _ _ hY1
      omega
    have e3 : A * Y ^ 3 * (34001 * Y ^ 6) * Z = 34001 * A * Y ^ 9 * Z := by ring
    have e4 : leafC K d A * (n + 1) ^ 9 * Z = (100000 + greedyK K + 34001 * A) * Y ^ 9 * Z := by
      rw [hYe, mul_pow]
      simp only [leafC]
      ring
    have s4 : 100000 * Y ^ 9 ≤ 100000 * Y ^ 9 * Z := Nat.le_mul_of_pos_right _ hZpos
    have s5 : greedyK K * Y ^ 9 ≤ greedyK K * Y ^ 9 * Z := Nat.le_mul_of_pos_right _ hZpos
    have e5 : (100000 + greedyK K + 34001 * A) * Y ^ 9 * Z =
        100000 * Y ^ 9 * Z + greedyK K * Y ^ 9 * Z + 34001 * A * Y ^ 9 * Z := by ring
    rw [e4, e5]
    omega

end UncrossingWires.Pseudo.Final
