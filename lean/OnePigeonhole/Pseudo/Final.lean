import OnePigeonhole.Pseudo.FinalHelpers
import OnePigeonhole.Pseudo.FinalLeaf

/-!
# The end-to-end theorem of the pseudocode layer

`Final.pseudo_main`: for every `ε > 0` there are one program `P`, constants `C`, `b`, `c`, such that for every `n` and every 3-CNF `F` on `n`
variables, with `W = c * (n + 1) ^ 3` and `env = [encF n F, n]`, the value of `P` is not zero exactly when `F` is satisfiable, and `P` costs at
most `C * (n + 1) ^ b * 2 ^ (ε * n)` word operations.

`P` is one fixed `Expr`, chosen after `ε` and before `n` and `F`. So `size P` and `stack P` are numbers that depend only on `ε`, and no statement
about them is needed: live words are at most `stack P` plus the environment, each of `W` bits.

`Final.pseudo_wide` is the same statement for every word size `W ≥ c * (n + 1) ^ 3` and every environment that continues below `encF n F :: n`,
with the same `P` and the same bound. The machine layer uses it.

The parameters are chosen in this order. From `ε` comes `k`, and from `k` comes `ℓ` for the branching tree, whose number of leaves is at most `2 ^ (n / k + 1)`.
A leaf of the tree has at most `d = 4 * ℓ ^ 2` occurrences of each variable. From `ε` and `d` comes `m`, with `26 * (1 + d) ≤ m` and the rate of a leaf below `ε / 2`
(`exists_m`). Then come the literal table, which depends only on `m`, and the constants of the cost. The branching tree of `SatBase` plays the role of the sparsification
lemma of Section 5 of `papers/one-pigeonhole/proof.tex`. Up to `K ^ 2` variables the program tries all assignments, as Section 1 says.
-/

namespace OnePigeonhole.Pseudo.Final

open Finset SatBase TransposeBase TransposeBase.Sat TransposeBase.General TransposeBase.Pseudo
  TransposeBase.Pseudo.Final OnePigeonhole.Pseudo.Leaf TransposeBase.Pseudo.CnfTree

/-! ### The top program -/

/-- The top program: exhaustive search up to `n₀` variables, and the branching tree above. -/
def topE (n₀ k ℓ m d : ℕ) (lt : Lits) : Expr :=
  .ite (.var 1) (.lit n₀) bruteE (treeE ℓ (fuelE k) (leafE m d lt))

theorem eval_topE {W n₀ k ℓ m d n w : ℕ} {lt : Lits} {rest : List ℕ} (h : n₀ < 2 ^ W) :
    eval W (topE n₀ k ℓ m d lt) (w :: n :: rest) =
      if n ≤ n₀ then eval W bruteE (w :: n :: rest)
      else eval W (treeE ℓ (fuelE k) (leafE m d lt)) (w :: n :: rest) := by
  have h1 : eval W (.lit n₀) (w :: n :: rest) = n₀ := eval_lit_small W h
  show (if eval W (.var 1) (w :: n :: rest) ≤ eval W (.lit n₀) (w :: n :: rest) then _ else _) = _
  rw [h1]
  rfl

theorem ops_topE {W n₀ k ℓ m d n w : ℕ} {lt : Lits} {rest : List ℕ} (h : n₀ < 2 ^ W) :
    ops W (topE n₀ k ℓ m d lt) (w :: n :: rest) =
      3 + if n ≤ n₀ then ops W bruteE (w :: n :: rest)
        else ops W (treeE ℓ (fuelE k) (leafE m d lt)) (w :: n :: rest) := by
  have h1 : eval W (.lit n₀) (w :: n :: rest) = n₀ := eval_lit_small W h
  show 1 + 1 + 1 + (if eval W (.var 1) (w :: n :: rest) ≤ eval W (.lit n₀) (w :: n :: rest) then _ else _) = _
  rw [h1]
  rfl

/-! ### The parameter `m` -/

/-- **The choice of `m`.** The rate of a leaf is small, and `m` is at least `26 * D`, for the number `D` of wires at a node. -/
theorem exists_m {D : ℕ} (hD : 1 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 80 ≤ m ∧ 26 * D ≤ m ∧ 10 * (D : ℝ) ^ 2 * ((Real.log m + 2) / m) ≤ ε / 20 := by
  have hε' : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨m, h80, h⟩ := TransposeBase.exists_good_L hD (ε := min ε 1 / 10) (by positivity)
  have e : min ε 1 / 10 / 2 = min ε 1 / 20 := by ring
  rw [e] at h
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  refine ⟨m, h80, ?_, h.trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))⟩
  have h1 : 10 * (D : ℝ) ^ 2 * ((Real.log m + 2) / m) ≤ 1 / 20 :=
    h.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have h2 : 10 * (D : ℝ) ^ 2 * (Real.log m + 2) ≤ m / 20 := by
    have h3 := mul_le_mul_of_nonneg_right h1 hm0.le
    have e2 : 10 * (D : ℝ) ^ 2 * ((Real.log m + 2) / m) * m = 10 * (D : ℝ) ^ 2 * (Real.log m + 2) := by
      field_simp
    rw [e2] at h3
    linarith
  have h3 : (26 * (D : ℝ)) ≤ m := by
    have h4 : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith
    have h5 : 10 * (D : ℝ) ^ 2 * 2 ≤ 10 * (D : ℝ) ^ 2 * (Real.log m + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  exact_mod_cast h3

/-! ### Many variables -/

/-- The cost constant of a leaf. -/
noncomputable def leafC (m d Kc dc : ℕ) : ℝ :=
  (100000 + 4 * (greedyK (m ^ 4) (Kof m) : ℝ) +
      (6 * (m : ℝ)) ^ 9 * (((m ^ 4 : ℕ) : ℝ) * (Kc + ((6 * m ^ 4 : ℕ) : ℝ) * (Kc + 68000)))) *
    ((Kof m + 17 * (1 + d) + 3 : ℕ) : ℝ) ^ (m ^ 4 + dc + 7)

/-- **Many variables: the branching tree decides `F`.** All sizes are hypotheses, on an opaque word size `W`. -/
theorem large_case {ε : ℝ} (hε : 0 < ε) {k ℓ d m Kc dc W n : ℕ} {lt : Lits}
    (hKd : ∀ S : Setup, S.m = m → ops S.W (coreE S.m S.lt S.nodeE) S.core ≤
      S.Q * S.Nq ^ S.Q * S.nS ^ 3 *
        (Kc * S.T ^ dc +
          S.L * 2 ^ (S.M / S.m) * (Kc * S.T ^ dc + 2 * (S.Unode * (S.v + 1)))))
    (hk : 0 < k) (hkε : 1 / (k : ℝ) ≤ ε / 4) (hℓ : 2 ≤ ℓ)
    (hℓrate : (20 * Real.log ℓ + 10) / ℓ ≤ 1 / (2 * (k : ℝ))) (hd : d = 4 * ℓ ^ 2) (hd3 : 3 ≤ d)
    (hm80 : 80 ≤ m) (hmD : 26 * (1 + d) ≤ m) (hmrate : 10 * (((1 + d : ℕ) : ℝ)) ^ 2 * ((Real.log m + 2) / m) ≤ ε / 20)
    (hlt : lt.Good m)
    (hth : Kof m ^ 2 ≤ n)
    (hW1 : (48 + (2 * d + Kof m + 12) ^ 2) * (n + 1) ^ 3 ≤ W)
    (hW2 : wConst m lt * (2 * Kof m + 20 * (1 + d) + 8) ^ 3 * (n + 1) ^ 3 ≤ W)
    (hW3 : (m ^ 4 * (1 + d) ^ 2 + 26 * lt.D * (1 + d) + 2) * (n + 1) ^ 3 ≤ W)
    (hT : TreeCtx W n ℓ) (hkW : k < W)
    (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3) (rest : List ℕ) :
    (eval W (treeE ℓ (fuelE k) (leafE m d lt)) (encF n F :: n :: rest) ≠ 0 ↔
      ∃ x, holdsFormula (literalHolds x) F) ∧
    ((3 + ops W (treeE ℓ (fuelE k) (leafE m d lt)) (encF n F :: n :: rest) : ℕ) : ℝ) ≤
      (9 + 4 * leafC m d Kc dc + 5 * ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ)) *
        ((n : ℝ) + 1) ^ (m ^ 4 + dc + 7 + 8) * (2 : ℝ) ^ (ε * n) := by
  have hA : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hCtx := hT.ctx
  have hWpow : ∀ {x : ℕ}, x < W → x < 2 ^ W := fun h => h.trans Nat.lt_two_pow_self
  have hC20 : 0 ≤ leafC m d Kc dc := by
    unfold leafC
    positivity
  -- the bound for one leaf
  set E2 : ℝ := (2 : ℝ) ^ (ε / 2 * n) with hE2
  have hE21 : 1 ≤ E2 := Real.one_le_rpow (by norm_num) (by positivity)
  set B : ℝ := leafC m d Kc dc * ((n : ℝ) + 1) ^ (m ^ 4 + dc + 7) * E2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hleaf : ∀ t, Reach hℓ (initialSparseState F hw ℓ hℓ) t → ∀ p,
      let E := encF n t.formula :: p :: encF n (initialSparseState F hw ℓ hℓ).formula :: encF n F :: n :: rest
      (eval W (leafE m d lt) E ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) t.formula) ∧
        ops W (leafE m d lt) E ≤ ⌊B⌋₊ := by
    intro t ht p E
    have hdeg : ∀ v, variableOccurrences t.formula v ≤ d := fun v => by
      rw [hd]
      exact noSparseRule_variable_bound t.formula ℓ hℓ t.width ht.isLeaf v
    obtain ⟨h1, h2⟩ := leaf_main hKd hlt (by omega) hmD (G := t.formula) t.width hd3 hdeg hth hW1 hW2 hW3
      p (encF n (initialSparseState F hw ℓ hℓ).formula) (encF n F) rest
    refine ⟨h1, Nat.le_floor (h2.trans ?_)⟩
    exact leaf_bound_real (Yc := Kof m + 17 * (1 + d) + 3) (b0 := m ^ 4 + dc + 7) (n := n)
      (pk := greedyK (m ^ 4) (Kof m)) (by omega) (by omega) (by positivity) (by positivity)
      (Real.exp_pos _).le (rate_real hm80 (by omega) hε hmrate) hE21
  -- the fuel
  have hW8 : 8 ≤ W := hCtx.eight_le
  have h2 : (2 : ℕ) < 2 ^ W := by
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW8
  have hG := Ctx.G_le_cap n
  have hcap := hCtx.cap_lt
  have hdivle : n / k ≤ n := Nat.div_le_self _ _
  have hcap2 : 2 * n + 1 < W := by omega
  have hfuelLt : n / k + 2 < W := by omega
  have hfuelRun : ∀ root : ℕ, CnfTree.Run W (fuelE k) (root :: encF n F :: n :: rest) (2 ^ (n / k + 2)) 6 := fun root =>
    run_pow2 (run_add (run_div (run_var (i := 2) (v := n) rfl) (run_lit (hWpow hkW))) (run_lit h2) (hWpow hfuelLt)) hfuelLt
  have hf2 : 2 ^ (n / k + 2) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hfuelLt
  obtain ⟨hV, hO⟩ := treeE_correct (rest := rest) hT hℓ F hw (hfuelRun _).1
    (leaves_le_fuel hℓ hk hℓrate _) hf2 hleaf
  refine ⟨hV, ?_⟩
  have hfops := (hfuelRun (encF n (initialSparseState F hw ℓ hℓ).formula)).2
  have hnat : 3 + ops W (treeE ℓ (fuelE k) (leafE m d lt)) (encF n F :: n :: rest) ≤
      9 + 2 ^ (n / k + 2) * (⌊B⌋₊ + treeP ℓ n) + treeP ℓ n := by omega
  have hcast : ((3 + ops W (treeE ℓ (fuelE k) (leafE m d lt)) (encF n F :: n :: rest) : ℕ) : ℝ) ≤
      9 + ((2 ^ (n / k + 2) : ℕ) : ℝ) * ((⌊B⌋₊ : ℝ) + (treeP ℓ n : ℝ)) + (treeP ℓ n : ℝ) := by
    exact_mod_cast hnat
  set E1 : ℝ := (2 : ℝ) ^ (ε / 4 * n) with hE1
  have hE11 : 1 ≤ E1 := Real.one_le_rpow (by norm_num) (by positivity)
  have hEE : E1 * E2 ≤ (2 : ℝ) ^ (ε * n) := by
    rw [hE1, hE2, ← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (0 : ℝ) ≤ ε * n := by positivity
    linarith
  have htreeP : (treeP ℓ n : ℝ) = ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ 8 := by
    simp only [treeP]
    push_cast
    ring
  have hc30 : (0 : ℝ) ≤ ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ) = c3 at htreeP hc30 ⊢
  exact hcast.trans (total_real (C2 := leafC m d Kc dc) (c3 := c3) (b0 := m ^ 4 + dc + 7) hA hE11 hE21 hEE hC20 hc30
    (fuel_real (n := n) hk hkε) (U := (⌊B⌋₊ : ℝ)) (Nat.cast_nonneg _) (Nat.floor_le hB0)
    (t := (treeP ℓ n : ℝ)) (Nat.cast_nonneg _) htreeP.le)

/-! ### The theorem -/

set_option linter.unusedVariables false in
/-- **The pseudocode theorem for every large word size.** The program `P` and the constants `C`, `b`, `c` are as in `pseudo_core`. The word size `W`
may be any number at least `c * (n + 1) ^ 3`, and the environment may continue below `encF n F :: n` with any words `rest`. The bound on the
operations depends on neither `W` nor `rest`. -/
theorem pseudo_wide (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Expr) (C : ℝ) (b c : ℕ), 8 ≤ c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3)
      (W : ℕ) (rest : List ℕ), c * (n + 1) ^ 3 ≤ W →
      let env := encF n F :: n :: rest
      (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
      (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n) := by
  classical
  -- the parameters
  obtain ⟨k, hk, hkε⟩ : ∃ k : ℕ, 0 < k ∧ 1 / (k : ℝ) ≤ ε / 4 := by
    obtain ⟨k, hk⟩ := exists_nat_gt (4 / ε)
    have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
    refine ⟨k, by exact_mod_cast hk0, ?_⟩
    rw [div_le_iff₀ hk0]
    rw [div_lt_iff₀ hε] at hk
    linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨ℓ, hℓ, hℓrate⟩ := exists_ell (ε := 2 / (k : ℝ)) (by positivity)
  have hℓrate' : (20 * Real.log ℓ + 10) / ℓ ≤ 1 / (2 * (k : ℝ)) := by
    refine hℓrate.trans (le_of_eq ?_)
    field_simp
    norm_num
  obtain ⟨d, hd⟩ : ∃ d, d = 4 * ℓ ^ 2 := ⟨_, rfl⟩
  have hd3 : 3 ≤ d := by
    have : 2 ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ 2
    omega
  obtain ⟨m, hm80, hmD, hmrate⟩ := exists_m (D := 1 + d) (by omega) hε
  obtain ⟨lt, hlt⟩ := exists_lits m
  obtain ⟨Kc, dc, hKd⟩ := coreE_ops_poly m
  -- the program and the constants
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = Kof m ^ 2 := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a1, a1 = 48 + (2 * d + Kof m + 12) ^ 2 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2, a2 = wConst m lt * (2 * Kof m + 20 * (1 + d) + 8) ^ 3 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a3, a3 = m ^ 4 * (1 + d) ^ 2 + 26 * lt.D * (1 + d) + 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = 8 + (10 * ℓ + 3) + (ℓ * ℓ + 1) + (n₀ + 1) + (k + 1) + a1 + a2 + a3 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℕ, C1 = (range (n₀ + 1)).sup bruteB := ⟨_, rfl⟩
  obtain ⟨C3, hC3⟩ : ∃ C3 : ℝ, C3 = 9 + 4 * leafC m d Kc dc + 5 * ((succC ℓ + bodyC ℓ + 100000 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hC30 : 0 ≤ C3 := by
    have : 0 ≤ leafC m d Kc dc := by
      unfold leafC
      positivity
    rw [hC3]
    positivity
  have hC10 : (0 : ℝ) ≤ C1 := Nat.cast_nonneg _
  refine ⟨topE n₀ k ℓ m d lt, (C1 : ℝ) + 3 + C3, m ^ 4 + dc + 7 + 8, c, by omega, ?_⟩
  intro n F hw W rest hcWn
  have hsup : n ≤ n₀ → bruteB n ≤ C1 := fun hn => by
    rw [hC1]
    exact Finset.le_sup (f := bruteB) (mem_range.mpr (Nat.lt_succ_of_le hn))
  have hA3 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hcW : ∀ x, x ≤ c → x * (n + 1) ^ 3 ≤ W := fun x hx => (Nat.mul_le_mul_right _ hx).trans hcWn
  have hcleW : c ≤ W := (Nat.le_mul_of_pos_right _ hA3).trans hcWn
  have hCtx0 : (2 * n + 2) ^ 3 ≤ W := by
    have e : (2 * n + 2) ^ 3 = 8 * (n + 1) ^ 3 := by ring
    rw [e]
    exact hcW 8 (by omega)
  have hdepth0 : 10 * n * ℓ + 3 ≤ W := by
    have h1 := hcW (10 * ℓ + 3) (by omega)
    have h2 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h3 : (10 * ℓ + 3) * (n + 1) ≤ (10 * ℓ + 3) * (n + 1) ^ 3 := Nat.mul_le_mul_left _ h2
    have e : (10 * ℓ + 3) * (n + 1) = 10 * n * ℓ + 10 * ℓ + 3 * n + 3 := by ring
    omega
  have hW1 := hcW a1 (by omega)
  have hW2 := hcW a2 (by omega)
  have hW3 := hcW a3 (by omega)
  rw [ha1] at hW1
  rw [ha2] at hW2
  rw [ha3] at hW3
  dsimp only
  have hWpow : W < 2 ^ W := Nat.lt_two_pow_self
  have hCtx : Ctx W n := ⟨hCtx0⟩
  have hn₀lt : n₀ < 2 ^ W := by omega
  have hA : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hE : (1 : ℝ) ≤ (2 : ℝ) ^ (ε * n) := Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hn : n ≤ n₀
  · -- few variables: exhaustive search
    refine ⟨?_, ?_⟩
    · rw [eval_topE hn₀lt, if_pos hn, bruteE_eval hCtx hw rest, ind_ne_zero]
    · rw [ops_topE hn₀lt, if_pos hn]
      refine const_le_bound (C' := (C1 : ℝ) + 3) ?_ (by positivity) (by linarith) hA hE
      have : 3 + ops W bruteE (encF n F :: n :: rest) ≤ C1 + 3 := by
        have := hsup hn
        have := bruteE_ops (W := W) (n := n) hCtx (encF n F) rest
        omega
      exact_mod_cast this
  · -- many variables: the branching tree
    have hnge : n₀ < n := not_le.mp hn
    have hth : Kof m ^ 2 ≤ n := by omega
    have hT : TreeCtx W n ℓ := ⟨hCtx, hdepth0, by omega⟩
    obtain ⟨h1, h2⟩ := large_case hε hKd hk hkε hℓ hℓrate' hd hd3 hm80 hmD hmrate hlt hth hW1 hW2 hW3 hT
      (by omega) F hw rest
    refine ⟨?_, ?_⟩
    · rw [eval_topE hn₀lt, if_neg hn]
      exact h1
    · rw [ops_topE hn₀lt, if_neg hn]
      rw [← hC3] at h2
      refine h2.trans ?_
      have hP : 0 ≤ ((n : ℝ) + 1) ^ (m ^ 4 + dc + 7 + 8) := by positivity
      have hEP : 0 ≤ (2 : ℝ) ^ (ε * n) := by positivity
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hP) hEP
      linarith

set_option linter.unusedVariables false in
/-- The pseudocode theorem without the statement that the input consists of words. -/
theorem pseudo_core (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Expr) (C : ℝ) (b c : ℕ), 8 ≤ c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3),
      let W := c * (n + 1) ^ 3
      let env := [encF n F, n]
      (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
      (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n) := by
  obtain ⟨P, C, b, c, hc, h⟩ := pseudo_wide ε hε
  exact ⟨P, C, b, c, hc, fun n F hw => h n F hw _ [] le_rfl⟩

set_option linter.unusedVariables false in
/-- **The pseudocode theorem.** For every `ε > 0` there are one program `P`, constants `C`, `b`, `c`, with `c > 0`, such that for every `n` and every
formula `F` with `n` variables and clauses of at most three literals, with `W = c * (n + 1) ^ 3` and `env = [encF n F, n]`, the input consists of words,
the value of `P` is not zero exactly when `F` is satisfiable, and the number of word operations is at most `C * (n + 1) ^ b * 2 ^ (ε * n)`.

By `eval_lt_word`, every value is then a word. `P` is chosen before `n` and `F`, so `size P` and `stack P` depend only on `ε`. That `stack P` bounds the
live words is the definition of `stack`, and no theorem here uses it; the compiler to a machine must prove it. -/
theorem pseudo_main (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Expr) (C : ℝ) (b c : ℕ), 0 < c ∧ ∀ (n : ℕ) (F : ClauseSet (SignedLiteral n)) (hw : ∀ C ∈ F, C.card ≤ 3),
      let W := c * (n + 1) ^ 3
      let env := [encF n F, n]
      (encF n F < 2 ^ W ∧ n < 2 ^ W) ∧
      (eval W P env ≠ 0 ↔ ∃ x, holdsFormula (literalHolds x) F) ∧
      (ops W P env : ℝ) ≤ C * ((n : ℝ) + 1) ^ b * 2 ^ (ε * n) := by
  obtain ⟨P, C, b, c, hc, h⟩ := pseudo_core ε hε
  refine ⟨P, C, b, c, by omega, fun n F hw => ⟨⟨encF_lt_word hw hc, ?_⟩, h n F hw⟩⟩
  refine lt_of_le_of_lt ?_ Nat.lt_two_pow_self
  have h1 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h2 : (n + 1) ^ 3 ≤ c * (n + 1) ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
  omega

end OnePigeonhole.Pseudo.Final
