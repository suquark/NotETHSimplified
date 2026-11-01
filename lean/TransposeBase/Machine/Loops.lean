import TransposeBase.Machine.Control

/-!
# `fold`, `sum`, `prod`

Instances of the loop lemma `go_loop2`. The potential of the loop rule is the operation count of `ops`, as it
stands after `k` iterations, times the budget of one word operation.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open StructuredCalls
open TransposeBase.Pseudo

variable {S : ℕ} [NeZero S]

local notation "u" => Function.update

theorem L2_good {W t N a k : ℕ} {map env : List ℕ} {m : Mem} (hg : Good W map env t m) :
    Good W map env (t + 1 + 1 + 1) (L2 W m t N a k) := hg.step.step.step

theorem L2_a {W t N a k : ℕ} {m : Mem} : L2 W m t N a k (11 + (t + 1)) = wordOf W a := by
  simp only [L2]
  rw [Function.update_of_ne (by omega), Function.update_self]

theorem L2_k {W t N a k : ℕ} {m : Mem} : L2 W m t N a k (11 + (t + 1 + 1)) = wordOf W k := by
  simp only [L2, Function.update_self]

/-! ### Fold -/

def foldBody (S : ℕ) [NeZero S] (Cb : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Cb ((t + 1) :: (t + 1 + 1) :: map) (t + 1 + 1 + 1)) (replaceC S (11 + (t + 1)) (11 + (t + 1 + 1 + 1)))

def foldE (S : ℕ) [NeZero S] (Cn Cs Cb : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Cn map t) (loop2C S (Cs map (t + 1)) (foldBody S Cb map t) t)

/-- The state of `fold` after `k` iterations. -/
private def foldVal (W : ℕ) (s b : Expr) (env : List ℕ) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun st j => eval W b (st :: j :: env)) (eval W s env)

/-- The operation count of `fold` after `k` iterations. -/
private def foldCost (W : ℕ) (n s b : Expr) (env : List ℕ) (k : ℕ) : ℕ :=
  ((List.range k).foldl (fun p j => (eval W b (p.1 :: j :: env), p.2 + 1 + ops W b (p.1 :: j :: env)))
    (eval W s env, 1 + ops W n env + ops W s env)).2

private theorem foldVal_succ (W : ℕ) (s b : Expr) (env : List ℕ) (k : ℕ) :
    foldVal W s b env (k + 1) = eval W b (foldVal W s b env k :: k :: env) := by
  simp [foldVal, List.range_succ, List.foldl_append]

private theorem foldCost_succ (W : ℕ) (n s b : Expr) (env : List ℕ) (k : ℕ) :
    foldCost W n s b env (k + 1) =
      foldCost W n s b env k + 1 + ops W b (foldVal W s b env k :: k :: env) := by
  simp only [foldCost, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [fold_ops_aux]
  rfl

theorem correct_fold {W : ℕ} {n s b : Expr} {Cn Cs Cb : List ℕ → ℕ → Cmd 10 S}
    (hn : Correct W n Cn) (hs : Correct W s Cs) (hb : Correct W b Cb) :
    Correct W (.fold n s b) (foldE S Cn Cs Cb) := by
  intro map env t m hg ht
  simp only [stack] at ht
  have hsn := stack_pos n
  have hss := stack_pos s
  have hsb := stack_pos b
  have henv := hg.env_lt
  set N := eval W n env with hNdef
  have hN : N < 2 ^ W := eval_lt_word W n env henv
  have hv : ∀ k ≤ N, foldVal W s b env k < 2 ^ W := by
    intro k
    induction k with
    | zero => exact fun _ => eval_lt_word W s env henv
    | succ k ih =>
      intro hk
      rw [foldVal_succ]
      refine eval_lt_word W b _ fun x hx => ?_
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ih (by omega)
      · omega
      · exact henv x hx
  have g₁ := hn map env t m hg (by omega)
  have hTsq := square_ge W
  have hTbig : 100 * W + 100 ≤ T W := by simp only [T]; omega
  have hinit := hs map env (t + 1) _ (hg.step (x := N)) (by omega)
  have hbody : ∀ k < N, Go (B W) (foldBody S Cb map t)
      (L2 W m t N (foldVal W s b env k) k) (L2 W m t N (foldVal W s b env (k + 1)) k)
      (ops W b (foldVal W s b env k :: k :: env) * T W + (11 * W + 11)) := by
    intro k hk
    set A := foldVal W s b env k with hA
    have hgg : Good W ((t + 1) :: (t + 1 + 1) :: map) (A :: k :: env) (t + 1 + 1 + 1) (L2 W m t N A k) :=
      ((L2_good hg).cons (by omega) L2_k (by omega)).cons (by omega) L2_a (hv k (by omega))
    have gb := hb _ _ _ _ hgg (by omega)
    rw [← foldVal_succ] at gb
    set A' := foldVal W s b env (k + 1) with hA'
    set M := u (L2 W m t N A k) (11 + (t + 1 + 1 + 1)) (wordOf W A') with hM
    have hgM : Good W map env (t + 1 + 1 + 1 + 1) M := (L2_good hg).step
    have e := ev_replace (S := S) (W := W) (x := 11 + (t + 1)) (y := 11 + (t + 1 + 1 + 1)) (wv := wordOf W A')
      (m := M) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hgM.clean (by simp [hM])
      (by simp) (by rw [hM, Function.update_of_ne (by omega), L2_a]; simp)
    have hmem : u (u M (11 + (t + 1)) (wordOf W A')) (11 + (t + 1 + 1 + 1)) [] = L2 W m t N A' k := by
      have h₃ := hg.empty (t + 1 + 1 + 1) (by omega)
      simp only [hM, L2]
      mem_eq'
    rw [hmem] at e
    exact GoQ.seq gb (go_routine e hgM.small (by omega))
  have hφ : ∀ k < N, foldCost W n s b env k * T W +
      ((ops W b (foldVal W s b env k :: k :: env) * T W + (11 * W + 11)) + (54 * W + 71)) + 1 ≤
      foldCost W n s b env (k + 1) * T W := by
    intro k _
    rw [foldCost_succ, add_mul, add_mul]
    omega
  have h0 : foldCost W n s b env 0 = 1 + ops W n env + ops W s env := rfl
  have hmono : foldCost W n s b env 0 * T W ≤ foldCost W n s b env N * T W :=
    phi_mono (Φ := fun k => foldCost W n s b env k * T W) hφ
  have h0' : foldCost W n s b env 0 * T W = T W + ops W n env * T W + ops W s env * T W := by
    rw [h0]
    ring
  have gl := go_loop2 (v := foldVal W s b env) (φ := foldCost W n s b env)
    (β := fun k => ops W b (foldVal W s b env k :: k :: env) * T W + (11 * W + 11))
    (t' := foldCost W n s b env N * T W - ops W n env * T W) hg (by omega) hN hv hinit
    hbody hφ (by omega)
  refine (GoQ.seq g₁ gl).mono ?_
  have hops : ops W (.fold n s b) env = foldCost W n s b env N := rfl
  rw [hops]
  omega

/-! ### Sum and product -/

def accBody (S : ℕ) [NeZero S] (core : Cmd 10 S) (Cb : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Cb ((t + 1 + 1) :: map) (t + 1 + 1 + 1)) (binC S core (11 + (t + 1)) (11 + (t + 1 + 1 + 1)))

def accE (S : ℕ) [NeZero S] (core : Cmd 10 S) (Init : ℕ → Cmd 10 S) (Cn Cb : List ℕ → ℕ → Cmd 10 S)
    (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Cn map t) (loop2C S (Init t) (accBody S core Cb map t) t)

private def accVal (W : ℕ) (op : ℕ → ℕ → ℕ) (i₀ : ℕ) (b : Expr) (env : List ℕ) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun st j => op st (eval W b (j :: env))) i₀

private def accCost (W : ℕ) (n b : Expr) (env : List ℕ) (k : ℕ) : ℕ :=
  1 + ops W n env + ((List.range k).map fun j => 1 + ops W b (j :: env)).sum

theorem correct_acc {W tc ti i₀ : ℕ} {core : Cmd 10 S} {Init : ℕ → Cmd 10 S} {op : ℕ → ℕ → ℕ} {E n b : Expr}
    {Cn Cb : List ℕ → ℕ → Cmd 10 S}
    (hcore : ∀ m₀ x y, Clean W m₀ → x < 2 ^ W → y < 2 ^ W →
      Ev core (u (u m₀ 0 (wordOf W x)) 1 (wordOf W y)) (u m₀ 0 (wordOf W (op x y))) tc)
    (hop : ∀ x y, op x y < 2 ^ W) (hi₀ : i₀ < 2 ^ W)
    (hInit : ∀ t (m' : Mem), 11 + t + 2 ≤ S → Clean W m' → m' (11 + (t + 1)) = [] →
      Ev (Init t) m' (u m' (11 + (t + 1)) (wordOf W i₀)) ti)
    (hval : ∀ env, eval W E env = accVal W op i₀ b env (eval W n env))
    (hops : ∀ env, ops W E env = accCost W n b env (eval W n env))
    (hstack : stack E = max (stack n) (3 + stack b))
    (htc : ti + (tc + 3 * (9 * W + 8)) + 66 * W + 100 ≤ T W)
    (hn : Correct W n Cn) (hb : Correct W b Cb) : Correct W E (accE S core Init Cn Cb) := by
  intro map env t m hg ht
  rw [hstack] at ht
  have hsn := stack_pos n
  have hsb := stack_pos b
  have hmax₁ := le_max_left (stack n) (3 + stack b)
  have hmax₂ := le_max_right (stack n) (3 + stack b)
  have henv := hg.env_lt
  set N := eval W n env with hNdef
  have hN : N < 2 ^ W := eval_lt_word W n env henv
  have hv : ∀ k ≤ N, accVal W op i₀ b env k < 2 ^ W := by
    intro k _
    cases k with
    | zero => exact hi₀
    | succ k =>
      simp only [accVal, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hop _ _
  have g₁ := hn map env t m hg (by omega)
  have hTsq := square_ge W
  have hg₁ : Good W map env (t + 1) (u m (11 + t) (wordOf W N)) := hg.step
  have hsm := hg₁.small
  have hinit : Go (B W) (Init t) (u m (11 + t) (wordOf W N))
      (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (accVal W op i₀ b env 0))) ti :=
    go_routine (hInit t _ (by omega) hg₁.clean (hg₁.empty _ le_rfl)) hsm (by omega)
  have hbody : ∀ k < N, Go (B W) (accBody S core Cb map t)
      (L2 W m t N (accVal W op i₀ b env k) k) (L2 W m t N (accVal W op i₀ b env (k + 1)) k)
      (ops W b (k :: env) * T W + (tc + 3 * (9 * W + 8))) := by
    intro k hk
    set A := accVal W op i₀ b env k with hA
    have hgg : Good W ((t + 1 + 1) :: map) (k :: env) (t + 1 + 1 + 1) (L2 W m t N A k) :=
      (L2_good hg).cons (by omega) L2_k (by omega)
    have gb := hb _ _ _ _ hgg (by omega)
    set Y := eval W b (k :: env) with hY
    have hYlt : Y < 2 ^ W := eval_lt_word W b _ hgg.env_lt
    have hA' : accVal W op i₀ b env (k + 1) = op A Y := by
      simp [accVal, List.range_succ, List.foldl_append, hA, hY]
    rw [hA']
    set M := u (L2 W m t N A k) (11 + (t + 1 + 1 + 1)) (wordOf W Y) with hM
    have hgM : Good W map env (t + 1 + 1 + 1 + 1) M := (L2_good hg).step
    have hclean : Clean W (u (u M (11 + (t + 1)) []) (11 + (t + 1 + 1 + 1)) []) :=
      (hgM.clean.high (by omega) _).high (by omega) _
    have e := ev_bin (S := S) (W := W) (x := 11 + (t + 1)) (y := 11 + (t + 1 + 1 + 1)) (wa := wordOf W A)
      (wb := wordOf W Y) (wr := wordOf W (op A Y)) (m := M) (core := core) (tc := tc) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hgM.clean
      (by rw [hM, Function.update_of_ne (by omega), L2_a]) (by simp [hM]) (by simp) (by simp) (by simp)
      (hcore _ _ _ hclean (hv k (by omega)) hYlt)
    have hmem : u (u M (11 + (t + 1)) (wordOf W (op A Y))) (11 + (t + 1 + 1 + 1)) [] = L2 W m t N (op A Y) k := by
      have h₃ := hg.empty (t + 1 + 1 + 1) (by omega)
      simp only [hM, L2]
      mem_eq'
    rw [hmem] at e
    exact GoQ.seq gb (go_routine e hgM.small (by omega))
  have hφ : ∀ k < N, accCost W n b env k * T W +
      ((ops W b (k :: env) * T W + (tc + 3 * (9 * W + 8))) + (54 * W + 71)) + 1 ≤
      accCost W n b env (k + 1) * T W := by
    intro k _
    have hstep : accCost W n b env (k + 1) = accCost W n b env k + 1 + ops W b (k :: env) := by
      simp [accCost, List.range_succ, List.map_append, List.sum_append]
      omega
    rw [hstep, add_mul, add_mul]
    omega
  have h0' : accCost W n b env 0 * T W = T W + ops W n env * T W := by
    simp only [accCost, List.range_zero, List.map_nil, List.sum_nil, add_zero]
    ring
  have hmono : accCost W n b env 0 * T W ≤ accCost W n b env N * T W :=
    phi_mono (Φ := fun k => accCost W n b env k * T W) hφ
  have gl := go_loop2 (v := accVal W op i₀ b env) (φ := accCost W n b env)
    (β := fun k => ops W b (k :: env) * T W + (tc + 3 * (9 * W + 8)))
    (t' := accCost W n b env N * T W - ops W n env * T W) hg (by omega) hN hv hinit
    hbody hφ (by omega)
  refine (go_eq (GoQ.seq g₁ gl) ?_).mono ?_
  · rw [hval]
  · rw [hops, ← hNdef]
    omega

/-- The accumulator of `sum` starts at the word of zero: a copy of the ruler. -/
def sumInit (S : ℕ) [NeZero S] (t : ℕ) : Cmd 10 S := copyC S 10 (11 + (t + 1))

/-- The accumulator of `prod` starts at `1 % 2 ^ W`. -/
def prodInit (S : ℕ) [NeZero S] (t : ℕ) : Cmd 10 S := .seq (litCore S 1) (mvC S 0 (11 + (t + 1)))

abbrev sumE (S : ℕ) [NeZero S] (Cn Cb : List ℕ → ℕ → Cmd 10 S) : List ℕ → ℕ → Cmd 10 S :=
  accE S (addCore S) (sumInit S) Cn Cb

abbrev prodE (S : ℕ) [NeZero S] (Cn Cb : List ℕ → ℕ → Cmd 10 S) : List ℕ → ℕ → Cmd 10 S :=
  accE S (mulCore S) (prodInit S) Cn Cb

theorem correct_sum {W : ℕ} {n b : Expr} {Cn Cb : List ℕ → ℕ → Cmd 10 S} (hS : 11 ≤ S)
    (hn : Correct W n Cn) (hb : Correct W b Cb) : Correct W (.sum n b) (sumE S Cn Cb) := by
  have hsq := square_ge W
  have hpos : 0 < 2 ^ W := by positivity
  refine correct_acc (op := fun x y => (x + y) % 2 ^ W) (i₀ := 0) (tc := 6000 * (W + 1) ^ 2 + 9 * (W + 1) + 8)
    (ti := 7 * W + 5) (fun m₀ x y hc hx hy => ev_add hS hc hx hy) (fun _ _ => Nat.mod_lt _ hpos) hpos ?_
    (fun _ => rfl) (fun _ => rfl) rfl (by simp only [T]; omega) hn hb
  intro t m' ht hc hm
  have := ev_copy' (S := S) (src := 10) (dst := 11 + (t + 1)) (L := W) (m := m') (x := wordOf W 0) (by omega)
    (by omega) (by omega) (by omega) (by norm_num) (by omega) hc.w8 (by rw [hc.ruler, wordOf_zero]) hm (by simp)
  exact this

theorem correct_prod {W : ℕ} {n b : Expr} {Cn Cb : List ℕ → ℕ → Cmd 10 S} (hS : 11 ≤ S)
    (hn : Correct W n Cn) (hb : Correct W b Cb) : Correct W (.prod n b) (prodE S Cn Cb) := by
  have hsq := square_ge W
  have hpos : 0 < 2 ^ W := by positivity
  refine correct_acc (op := fun x y => (x * y) % 2 ^ W) (i₀ := 1 % 2 ^ W)
    (tc := 6000 * (W + 1) ^ 2 + 9 * (W + 1) + 8) (ti := 29 * W + 48)
    (fun m₀ x y hc hx hy => ev_mul hS hc hx hy) (fun _ _ => Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) ?_
    (fun _ => rfl) (fun _ => rfl) rfl (by simp only [T]; omega) hn hb
  intro t m' ht hc hm
  have e₁ := ev_lit (S := S) hS hc 1
  have e₂ := ev_mv (S := S) (src := 0) (dst := 11 + (t + 1)) (L := W) (m := u m' 0 (wordOf W (1 % 2 ^ W)))
    (x := wordOf W (1 % 2 ^ W)) (by omega) (by omega) (by omega) (by omega) (by norm_num) (by omega)
    (by rw [Function.update_of_ne (by omega)]; exact hc.w8) (by simp)
    (by rw [Function.update_of_ne (by omega)]; exact hm) (by simp)
  have hmem : u (u (u m' 0 (wordOf W (1 % 2 ^ W))) (11 + (t + 1)) (wordOf W (1 % 2 ^ W))) 0 [] =
      u m' (11 + (t + 1)) (wordOf W (1 % 2 ^ W)) := by
    have := hc.w0
    mem_eq'
  rw [hmem] at e₂
  exact (EvQ.seq e₁ e₂).mono (by omega)

end TransposeBase.Machine
