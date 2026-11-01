import UncrossingWires.Greedy
import UncrossingWires.Pseudo.Prog

/-!
# The greedy placement as a program

`run_greedyE`: the value of `greedyE` is `Greedy.table`, and its cost is at most `greedyK K * (m + v + 1) ^ 3`.

The sizes come from `Place.Bd`, and the tables of the wires from `Place.NetT`.
-/

namespace UncrossingWires.Pseudo

open Finset TransposeBase.Pseudo TransposeBase.Pseudo.Leaf
open TransposeBase.Pseudo.Place (fld Bd NetT fieldE setE eval_fieldE ops_fieldE eval_setE ops_setE)

/-- The bound on the operations of `loadE`. -/
def loadCost (m : ℕ) : ℕ := 1 + 1 + m * (100 + 1)

/-- The bound on the operations of `scoreE`. -/
def scoreCost (m : ℕ) : ℕ := 1 + 1 + m * (64 + 2 * loadCost m + 1)

/-- The bound on the operations of `pickE`. -/
def pickCost (K m : ℕ) : ℕ := 1 + 1 + 1 + K * (1 + scoreCost m + scoreCost m + (1 + 1) + 1)

/-- The bound on the operations of `greedyE`. -/
def greedyCost (K m v : ℕ) : ℕ := 1 + 1 + 1 + v * (1 + (1 + 1 + 1 + (pickCost K m + (1 + 1 + 1))) + 8 + 1)

/-- The constant of `greedyE`. -/
def greedyK (K : ℕ) : ℕ := 600 * (K + 1)

namespace GreedySpec

variable {W m v fw K n tT hT : ℕ} {tail head : Fin m → Fin v}

/-- A loop with a state. The states are the values of `T`. -/
theorem run_fold {a s b : Expr} {env : List ℕ} {k ca cs B : ℕ} {T : ℕ → ℕ} (ha : Run W a env k ca)
    (hs : Run W s env (T 0) cs) (h : ∀ i < k, Run W b (T i :: i :: env) (T (i + 1)) B) :
    Run W (.fold a s b) env (T k) (1 + ca + cs + k * (B + 1)) := by
  have key : ∀ j ≤ k, (List.range j).foldl (fun st i => eval W b (st :: i :: env)) (T 0) = T j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih (by omega)]
      exact (h j (by omega)).1
  refine ⟨by rw [eval_fold, ha.1, hs.1]; exact key k le_rfl, ?_⟩
  have h1 := ops_fold_le W a s b env (fun i st => st = T i) (B := B) hs.1
    (fun i st hi hst => by
      subst hst
      rw [ha.1] at hi
      exact (h i hi).1)
    (fun i st hi hst => by
      subst hst
      rw [ha.1] at hi
      exact (h i hi).2)
  rw [ha.1] at h1
  have := ha.2
  have := hs.2
  omega

theorem run_field (B : Bd W m v fw K) {t i f tv iv : ℕ} {env : List ℕ} (ht : env.getD t 0 = tv)
    (hi : env.getD i 0 = iv) (hf : env.getD f 0 = fw) (hiv : iv < v) :
    Run W (fieldE t i f) env (fld fw tv iv) 9 :=
  ⟨eval_fieldE ht hi hf (B.idx_lt (by omega)) B.fw_lt, (ops_fieldE W t i f env).le⟩

/-! ### Reading the tables of the wires -/

theorem load_eq_range (N : NetT fw tT hT tail head) (R α x y : ℕ) :
    Greedy.load fw tail head R α x y =
      ∑ i ∈ range m, if fld fw hT i < α ∧ fld fw R (fld fw tT i) = x ∧ fld fw R (fld fw hT i) = y then 1 else 0 := by
  rw [Finset.sum_range]
  refine sum_congr rfl fun e _ => ?_
  rw [N.tail_eq, N.head_eq]

theorem score_eq_range (N : NetT fw tT hT tail head) (R α y : ℕ) :
    Greedy.score fw tail head R α y =
      ∑ i ∈ range m, if fld fw hT i = α then Greedy.load fw tail head R α (fld fw R (fld fw tT i)) y else 0 := by
  rw [Finset.sum_range]
  refine sum_congr rfl fun e _ => ?_
  rw [N.tail_eq, N.head_eq]

theorem load_le (R α x y : ℕ) : Greedy.load fw tail head R α x y ≤ m := by
  calc Greedy.load fw tail head R α x y ≤ ∑ _e : Fin m, 1 := sum_le_sum fun e _ => by split_ifs <;> omega
    _ = m := by simp

theorem score_le (R α y : ℕ) : Greedy.score fw tail head R α y ≤ m * m := by
  calc Greedy.score fw tail head R α y ≤ ∑ _e : Fin m, m := sum_le_sum fun e _ => by
        split_ifs
        · exact load_le _ _ _ _
        · omega
    _ = m * m := by simp

/-! ### The programs -/

section Run

variable {im it ih ifw iR iα : ℕ} {env : List ℕ} {R α : ℕ}

theorem run_loadE (B : Bd W m v fw K) (N : NetT fw tT hT tail head) {ix iy x y : ℕ}
    (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw)
    (hR : env.getD iR 0 = R) (hα : env.getD iα 0 = α) (hx : env.getD ix 0 = x) (hy : env.getD iy 0 = y) :
    Run W (loadE im it ih ifw iR iα ix iy) env (Greedy.load fw tail head R α x y) (loadCost m) := by
  rw [load_eq_range N]
  refine Run.sum (Run.var hm) le_rfl (B := 100) (fun i hi => ?_) ?_
  · have htv : fld fw tT i < v := by
      have := N.tail_eq ⟨i, hi⟩
      simp only at this
      rw [this]
      exact (tail _).2
    have hhv : fld fw hT i < v := by
      have := N.head_eq ⟨i, hi⟩
      simp only at this
      rw [this]
      exact (head _).2
    have him : i < v + m := by omega
    have hl1 : (1 : ℕ) < 2 ^ W := B.one_lt
    have h0 : (0 : ℕ) < 2 ^ W := by positivity
    have r1 : Run W (fieldE (it + 1) 0 (ifw + 1)) (i :: env) (fld fw tT i) 9 :=
      ⟨eval_fieldE (by simpa using ht) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
        (ops_fieldE W _ _ _ _).le⟩
    have r2 : Run W (fieldE (ih + 2) 1 (ifw + 2)) (fld fw tT i :: i :: env) (fld fw hT i) 9 :=
      ⟨eval_fieldE (by simpa using hh) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
        (ops_fieldE W _ _ _ _).le⟩
    generalize hE : fld fw hT i :: fld fw tT i :: i :: env = E
    have r3 : Run W (fieldE (iR + 3) 1 (ifw + 3)) E (fld fw R (fld fw tT i)) 9 :=
      run_field B (by rw [← hE]; simpa using hR) (by rw [← hE]; rfl) (by rw [← hE]; simpa using hf) htv
    have r4 : Run W (fieldE (iR + 3) 0 (ifw + 3)) E (fld fw R (fld fw hT i)) 9 :=
      run_field B (by rw [← hE]; simpa using hR) (by rw [← hE]; rfl) (by rw [← hE]; simpa using hf) hhv
    have vx : Run W (.var (ix + 3)) E x 1 := Run.var (by rw [← hE]; simpa using hx)
    have vy : Run W (.var (iy + 3)) E y 1 := Run.var (by rw [← hE]; simpa using hy)
    have l0 : Run W (.lit 0) E 0 1 := Run.lit h0
    have l1 : Run W (.lit 1) E 1 1 := Run.lit hl1
    have c1 : Run W (eqX (fieldE (iR + 3) 0 (ifw + 3)) (.var (iy + 3)) (.lit 1) (.lit 0)) E
        (if fld fw R (fld fw hT i) = y then 1 else 0) (2 + 2 * (9 + 1) + 2 * (1 + 1)) :=
      Run.eqX r4 vy (fun h => l1.eq (if_pos h).symm) (fun h => l0.eq (if_neg h).symm)
    have c2 : Run W (eqX (fieldE (iR + 3) 1 (ifw + 3)) (.var (ix + 3))
          (eqX (fieldE (iR + 3) 0 (ifw + 3)) (.var (iy + 3)) (.lit 1) (.lit 0)) (.lit 0)) E
        (if fld fw R (fld fw tT i) = x ∧ fld fw R (fld fw hT i) = y then 1 else 0)
        (2 + 2 * (9 + 1) + 2 * ((2 + 2 * (9 + 1) + 2 * (1 + 1)) + 1)) :=
      Run.eqX r3 vx (fun h => c1.eq (by simp [h])) (fun h => l0.eq (by simp [h]))
    have c3 : Run W (.ite (.var (iα + 3)) (.var 0) (.lit 0)
          (eqX (fieldE (iR + 3) 1 (ifw + 3)) (.var (ix + 3))
            (eqX (fieldE (iR + 3) 0 (ifw + 3)) (.var (iy + 3)) (.lit 1) (.lit 0)) (.lit 0))) E
        (if fld fw hT i < α ∧ fld fw R (fld fw tT i) = x ∧ fld fw R (fld fw hT i) = y then 1 else 0)
        (1 + 1 + 1 + (1 + (2 + 2 * (9 + 1) + 2 * ((2 + 2 * (9 + 1) + 2 * (1 + 1)) + 1)))) :=
      Run.ite (x := α) (y := fld fw hT i) (Run.var (by rw [← hE]; simpa using hα)) (Run.var (by rw [← hE]; rfl))
        (fun h => l0.eq (if_neg fun hh => by have := hh.1; omega).symm)
        (fun h => c2.eq (by
          have h' : fld fw hT i < α := not_le.mp h
          simp [h']))
    subst hE
    exact (Run.letE r1 (Run.letE r2 c3)).mono (by norm_num)
  · refine lt_of_le_of_lt ?_ (B.m_lt.trans B.pow_lt)
    rw [← load_eq_range N]
    exact load_le _ _ _ _

theorem run_scoreE (B : Bd W m v fw K) (N : NetT fw tT hT tail head) {iy y : ℕ}
    (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw)
    (hR : env.getD iR 0 = R) (hα : env.getD iα 0 = α) (hy : env.getD iy 0 = y) :
    Run W (scoreE im it ih ifw iR iα iy) env (Greedy.score fw tail head R α y) (scoreCost m) := by
  rw [score_eq_range N]
  refine Run.sum (Run.var hm) le_rfl (B := 64 + 2 * loadCost m) (fun i hi => ?_) ?_
  · have htv : fld fw tT i < v := by
      have := N.tail_eq ⟨i, hi⟩
      simp only at this
      rw [this]
      exact (tail _).2
    have r1 : Run W (fieldE (ih + 1) 0 (ifw + 1)) (i :: env) (fld fw hT i) 9 :=
      ⟨eval_fieldE (by simpa using hh) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
        (ops_fieldE W _ _ _ _).le⟩
    have r2 : Run W (fieldE (it + 1) 0 (ifw + 1)) (i :: env) (fld fw tT i) 9 :=
      ⟨eval_fieldE (by simpa using ht) (by simp) (by simpa using hf) (B.idx_lt (by omega)) B.fw_lt,
        (ops_fieldE W _ _ _ _).le⟩
    have r3 : Run W (fieldE (iR + 2) 0 (ifw + 2)) (fld fw tT i :: i :: env) (fld fw R (fld fw tT i)) 9 :=
      run_field B (by simpa using hR) (by simp) (by simpa using hf) htv
    generalize hE : fld fw R (fld fw tT i) :: fld fw tT i :: i :: env = E
    have r4 : Run W (loadE (im + 3) (it + 3) (ih + 3) (ifw + 3) (iR + 3) (iα + 3) 0 (iy + 3)) E
        (Greedy.load fw tail head R α (fld fw R (fld fw tT i)) y) (loadCost m) :=
      run_loadE B N (by rw [← hE]; simpa using hm) (by rw [← hE]; simpa using ht) (by rw [← hE]; simpa using hh)
        (by rw [← hE]; simpa using hf) (by rw [← hE]; simpa using hR) (by rw [← hE]; simpa using hα)
        (by rw [← hE]; rfl) (by rw [← hE]; simpa using hy)
    subst hE
    have r5 := Run.letE r2 (Run.letE r3 r4)
    have l0 : Run W (.lit 0) (i :: env) 0 1 := Run.lit (by positivity)
    have vα : Run W (.var (iα + 1)) (i :: env) α 1 := Run.var (by simpa using hα)
    have r6 := Run.eqX (r := if fld fw hT i = α then Greedy.load fw tail head R α (fld fw R (fld fw tT i)) y else 0)
      r1 vα (fun h => r5.eq (if_pos h).symm) (fun h => l0.eq (if_neg h).symm)
    exact r6.mono (by omega)
  · rw [← score_eq_range N]
    exact lt_of_le_of_lt (score_le _ _ _) (B.mul_lt B.m_lt B.m_lt)

theorem run_pickE (B : Bd W m v fw K) (N : NetT fw tT hT tail head)
    (hm : env.getD im 0 = m) (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) (hf : env.getD ifw 0 = fw)
    (hR : env.getD iR 0 = R) (hα : env.getD iα 0 = α) :
    Run W (pickE K im it ih ifw iR iα) env (Greedy.best fw tail head R α K) (pickCost K m) := by
  have hbody : ∀ y < K, Run W (.ite (scoreE (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 0)
      (scoreE (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 1) (.var 0) (.var 1))
      (Greedy.best fw tail head R α y :: y :: env) (Greedy.best fw tail head R α (y + 1))
      (1 + scoreCost m + scoreCost m + (1 + 1)) := by
    intro y _
    generalize hb : Greedy.best fw tail head R α y = b
    generalize hE : b :: y :: env = E
    have s0 : Run W (scoreE (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 0) E
        (Greedy.score fw tail head R α b) (scoreCost m) :=
      run_scoreE B N (by rw [← hE]; simpa using hm) (by rw [← hE]; simpa using ht) (by rw [← hE]; simpa using hh)
        (by rw [← hE]; simpa using hf) (by rw [← hE]; simpa using hR) (by rw [← hE]; simpa using hα) (by rw [← hE]; rfl)
    have s1 : Run W (scoreE (im + 2) (it + 2) (ih + 2) (ifw + 2) (iR + 2) (iα + 2) 1) E
        (Greedy.score fw tail head R α y) (scoreCost m) :=
      run_scoreE B N (by rw [← hE]; simpa using hm) (by rw [← hE]; simpa using ht) (by rw [← hE]; simpa using hh)
        (by rw [← hE]; simpa using hf) (by rw [← hE]; simpa using hR) (by rw [← hE]; simpa using hα) (by rw [← hE]; rfl)
    have e : Greedy.best fw tail head R α (y + 1) =
        if Greedy.score fw tail head R α b ≤ Greedy.score fw tail head R α y then b else y := by
      rw [Greedy.best, hb]
    rw [e]
    exact Run.ite s0 s1
      (fun h => (Run.var (by rw [← hE]; rfl)).eq (if_pos h).symm)
      (fun h => (Run.var (by rw [← hE]; rfl)).eq (if_neg h).symm)
  exact run_fold (T := Greedy.best fw tail head R α) (Run.lit B.lit_K) (Run.lit (by positivity)) hbody

/-- **The placement as a program.** -/
theorem run_greedyE (B : Bd W m v fw K) (N : NetT fw tT hT tail head) {inn iv : ℕ}
    (hn : env.getD inn 0 = n) (hm : env.getD im 0 = m) (hv : env.getD iv 0 = v) (hf : env.getD ifw 0 = fw)
    (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) :
    Run W (greedyE K inn im iv ifw it ih) env (Greedy.table fw n K tail head v) (greedyCost K m v) := by
  have hK := B.hK
  have hK2 : K ≤ 2 ^ fw := B.K_lt.le
  refine run_fold (T := Greedy.table fw n K tail head) (Run.var hv) (Run.lit (by positivity)) ?_
  intro a ha
  generalize hRd : Greedy.table fw n K tail head a = Ra
  have hRa : Ra < 2 ^ (a * fw) := by
    rw [← hRd]
    exact Greedy.table_lt hK hK2 a
  have hwlt : Greedy.word fw n K tail head Ra a < K := Greedy.word_lt hK _ _
  generalize hE : Ra :: a :: env = E
  have hpick : Run W (pickE K (im + 2) (it + 2) (ih + 2) (ifw + 2) 0 1) E
      (Greedy.best fw tail head Ra a K) (pickCost K m) :=
    run_pickE B N (by rw [← hE]; simpa using hm) (by rw [← hE]; simpa using ht) (by rw [← hE]; simpa using hh)
      (by rw [← hE]; simpa using hf) (by rw [← hE]; rfl) (by rw [← hE]; rfl)
  have hmod : Run W (.mod (.var 1) (.lit K)) E (a % K) (1 + 1 + 1) :=
    Run.mod (Run.var (by rw [← hE]; rfl)) (Run.lit B.lit_K)
  have hword : Run W (.ite (.var (inn + 2)) (.var 1) (pickE K (im + 2) (it + 2) (ih + 2) (ifw + 2) 0 1)
      (.mod (.var 1) (.lit K))) E (Greedy.word fw n K tail head Ra a)
      (1 + 1 + 1 + (pickCost K m + (1 + 1 + 1))) :=
    Run.ite (x := n) (y := a) (Run.var (by rw [← hE]; simpa using hn)) (Run.var (by rw [← hE]; rfl))
      (fun h => hpick.eq (if_pos h).symm) (fun h => hmod.eq (if_neg h).symm)
  generalize hw : Greedy.word fw n K tail head Ra a = w at hwlt hword
  have hw2 : w < 2 ^ fw := hwlt.trans_le hK2
  have hidx : a * fw < W := B.idx_lt (by omega)
  have hsum : Ra + w * 2 ^ (a * fw) < 2 ^ W :=
    (Place.add_mul_lt hRa hw2).trans_le (Nat.pow_le_pow_right (by norm_num) (B.idx_lt (by omega)).le)
  have hset : Run W (setE 1 0 2 (ifw + 3)) (w :: E) (Ra + w * 2 ^ (a * fw)) 8 := by
    subst hE
    have g : (w :: Ra :: a :: env).getD (ifw + 3) 0 = fw := by simpa using hf
    refine ⟨?_, (ops_setE W _ _ _ _ _).le⟩
    rw [eval_setE (by rw [g]; exact hidx) (by rw [g]; exact hsum), g]
    rfl
  have e : Greedy.table fw n K tail head (a + 1) = Ra + w * 2 ^ (a * fw) := by
    rw [Greedy.table, hRd, hw]
  rw [e]
  subst hE
  exact Run.letE hword hset

end Run

/-! ### The cost -/

theorem greedyCost_le (K m v : ℕ) : greedyCost K m v ≤ greedyK K * (m + v + 1) ^ 3 := by
  generalize hA : m + v + 1 = A
  have hA1 : 1 ≤ A := by omega
  have hmA : m ≤ A := by omega
  have hvA : v ≤ A := by omega
  have hAA : A ≤ A ^ 2 := Nat.le_self_pow (by norm_num) A
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA1
  have hA3 : 1 ≤ A ^ 3 := Nat.one_le_pow _ _ hA1
  have h1 : loadCost m ≤ 103 * A := by
    unfold loadCost
    omega
  have h2 : scoreCost m ≤ 273 * A ^ 2 := by
    have e : A * (271 * A) = 271 * A ^ 2 := by ring
    have h3 : m * (64 + 2 * loadCost m + 1) ≤ A * (271 * A) := Nat.mul_le_mul hmA (by omega)
    unfold scoreCost
    omega
  have h3 : pickCost K m ≤ 553 * (K + 1) * A ^ 2 := by
    have e : (K + 1) * (550 * A ^ 2) = 550 * (K + 1) * A ^ 2 := by ring
    have h4 : K * (1 + scoreCost m + scoreCost m + (1 + 1) + 1) ≤ (K + 1) * (550 * A ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h5 : 1 ≤ (K + 1) * A ^ 2 := Nat.mul_pos (by omega) (by omega)
    have e2 : 553 * (K + 1) * A ^ 2 = 553 * ((K + 1) * A ^ 2) := by ring
    have e3 : 550 * (K + 1) * A ^ 2 = 550 * ((K + 1) * A ^ 2) := by ring
    unfold pickCost
    omega
  have h4 : greedyCost K m v ≤ 600 * ((K + 1) * A ^ 3) := by
    have e : A * (569 * (K + 1) * A ^ 2) = 569 * ((K + 1) * A ^ 3) := by ring
    have e2 : 553 * (K + 1) * A ^ 2 = 553 * ((K + 1) * A ^ 2) := by ring
    have e3 : 569 * (K + 1) * A ^ 2 = 569 * ((K + 1) * A ^ 2) := by ring
    have h5 : 1 ≤ (K + 1) * A ^ 2 := Nat.mul_pos (by omega) (by omega)
    have h6 : v * (1 + (1 + 1 + 1 + (pickCost K m + (1 + 1 + 1))) + 8 + 1) ≤ A * (569 * (K + 1) * A ^ 2) :=
      Nat.mul_le_mul hvA (by omega)
    have h7 : 1 ≤ (K + 1) * A ^ 3 := Nat.mul_pos (by omega) (by omega)
    unfold greedyCost
    omega
  calc greedyCost K m v ≤ 600 * ((K + 1) * A ^ 3) := h4
    _ = greedyK K * A ^ 3 := by
      unfold greedyK
      ring

end GreedySpec

/-- **The placement as a program**: value and cost. -/
theorem greedy_spec {W m v fw K n tT hT : ℕ} {tail head : Fin m → Fin v} (B : Bd W m v fw K)
    (N : NetT fw tT hT tail head) {inn im iv ifw it ih : ℕ} {env : List ℕ}
    (hn : env.getD inn 0 = n) (hm : env.getD im 0 = m) (hv : env.getD iv 0 = v) (hf : env.getD ifw 0 = fw)
    (ht : env.getD it 0 = tT) (hh : env.getD ih 0 = hT) :
    Run W (greedyE K inn im iv ifw it ih) env (Greedy.table fw n K tail head v) (greedyK K * (m + v + 1) ^ 3) :=
  (GreedySpec.run_greedyE B N hn hm hv hf ht hh).mono (GreedySpec.greedyCost_le K m v)

end UncrossingWires.Pseudo
