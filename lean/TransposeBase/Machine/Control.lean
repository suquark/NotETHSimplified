import TransposeBase.Machine.Slots

/-!
# Conditionals, let, and loops with one accumulator

`ite` compares the slots, clears them, and runs only the chosen branch. A loop keeps its bound in the slot `t`,
an accumulator in the slot `t + 1` and the counter, ascending, in the slot `t + 2`; the loop guard compares
the counter with the bound. `fold`, `sum` and `prod` are instances of one lemma, `go_loop2`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TransposeBase.Machine

open OAI.Algorithms.SubexponentialSAT
open StructuredCalls
open TransposeBase.Pseudo

variable {S : ℕ} [NeZero S]

local notation "u" => Function.update

/-! ### Conditional -/

/-- `ite a b c d`. The register holds `b < a`, so its `true` branch is `d`. -/
def iteE (S : ℕ) [NeZero S] (Ca Cb Cc Cd : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Ca map t) (.seq (Cb map (t + 1)) (.seq (cmpC S (11 + (t + 1)) (11 + t))
    (.ite 0 (.seq (clearC S (11 + t)) (.seq (clearC S (11 + (t + 1))) (Cd map t)))
      (.seq (clearC S (11 + t)) (.seq (clearC S (11 + (t + 1))) (Cc map t))))))

theorem correct_ite {W : ℕ} {a b c d : Expr} {Ca Cb Cc Cd : List ℕ → ℕ → Cmd 10 S}
    (ha : Correct W a Ca) (hb : Correct W b Cb) (hc : Correct W c Cc) (hd : Correct W d Cd) :
    Correct W (.ite a b c d) (iteE S Ca Cb Cc Cd) := by
  intro map env t m hg ht
  simp only [stack] at ht
  have hsb := stack_pos b
  have henv := hg.env_lt
  have hA := eval_lt_word W a env henv
  have hB := eval_lt_word W b env henv
  have g₁ := ha map env t m hg (by omega)
  have hg₁ : Good W map env (t + 1) (u m (11 + t) (wordOf W (eval W a env))) := hg.step
  have g₂ := hb map env (t + 1) _ hg₁ (by omega)
  set M := u (u m (11 + t) (wordOf W (eval W a env))) (11 + (t + 1)) (wordOf W (eval W b env)) with hM
  have hg₂ : Good W map env (t + 1 + 1) M := hg₁.step
  have h₁ := hg.empty t le_rfl
  have h₂ := hg.empty (t + 1) (by omega)
  have ecmp := ev_cmp (S := S) (W := W) (x := 11 + (t + 1)) (y := 11 + t) (a := eval W b env)
    (b := eval W a env) (m := M) (by omega) (by omega) (by omega) (by omega) (by omega) hg₂.clean
    (by simp [hM]) (by simp [hM, Function.update_apply]) hB hA
  have gcmp := go_routine ecmp hg₂.small (by have := square_ge W; simp only [T]; omega)
  -- Both branches clear the two operands and continue from `m`.
  have clear2 : ∀ {X : Cmd 10 S} {tx : ℕ} {m' : Mem}, Go (B W) X m m' tx →
      Go (B W) (.seq (clearC S (11 + t)) (.seq (clearC S (11 + (t + 1))) X)) M m' (4 * W + 6 + tx) := by
    intro X tx m' hX
    have e₁ := ev_clear' (S := S) (i := 11 + t) (L := W) (by omega) M (by simp [hM, Function.update_apply])
    have e₂ := ev_clear' (S := S) (i := 11 + (t + 1)) (L := W) (by omega) (u M (11 + t) [])
      (by simp [hM, Function.update_apply])
    have hmem : u (u M (11 + t) []) (11 + (t + 1)) [] = m := by
      simp only [hM]
      mem_eq'
    rw [hmem] at e₂
    have hs := hg₂.small
    have g₁' := go_routine e₁ hs (by have := square_ge W; simp only [T]; omega)
    have g₂' := go_routine e₂ (by small_tac hs) (by have := square_ge W; simp only [T]; omega)
    exact (GoQ.seq g₁' (GoQ.seq g₂' hX)).mono (by omega)
  have hcost : ops W (.ite a b c d) env * T W = T W + ops W a env * T W + ops W b env * T W +
      (if eval W a env ≤ eval W b env then ops W c env else ops W d env) * T W := by
    simp only [ops]
    ring
  rw [hcost]
  have hlast := GoQ.ite (t₂ := 4 * W + 6 +
      (if eval W a env ≤ eval W b env then ops W c env else ops W d env) * T W)
    (y := .seq (clearC S (11 + t)) (.seq (clearC S (11 + (t + 1))) (Cd map t)))
    (no := .seq (clearC S (11 + t)) (.seq (clearC S (11 + (t + 1))) (Cc map t)))
    (m₂ := u m (11 + t) (wordOf W (eval W (.ite a b c d) env))) (Q := fun _ => True) gcmp
    (fun hv => by
      have hlt : eval W b env < eval W a env := by simpa using hv
      have hnle : ¬ eval W a env ≤ eval W b env := by omega
      simp only [eval, if_neg hnle]
      exact clear2 (hd map env t m hg (by omega)))
    (fun hv => by
      have hle : eval W a env ≤ eval W b env := by simpa using hv
      simp only [eval, if_pos hle]
      exact clear2 (hc map env t m hg (by omega)))
  refine (GoQ.seq g₁ (GoQ.seq g₂ hlast)).mono ?_
  have := square_ge W
  simp only [T] at *
  omega

/-! ### Let -/

/-- `letE a b`: the value of `a` stays in the slot `t` while `b` runs. -/
def letC (S : ℕ) [NeZero S] (Ca Cb : List ℕ → ℕ → Cmd 10 S) (map : List ℕ) (t : ℕ) : Cmd 10 S :=
  .seq (Ca map t) (.seq (Cb (t :: map) (t + 1)) (.seq (clearC S (11 + t)) (mvC S (11 + (t + 1)) (11 + t))))

/-- Replace the slot `x` by the slot `y`, and empty `y`. -/
def replaceC (S : ℕ) [NeZero S] (x y : ℕ) : Cmd 10 S := .seq (clearC S x) (mvC S y x)

theorem ev_replace {W x y : ℕ} {wv : List Bool} {m : Mem} (hS : 11 ≤ S) (hx : x < S) (hy : y < S) (hx11 : 11 ≤ x)
    (hy11 : 11 ≤ y) (hne : x ≠ y) (hc : Clean W m) (hmy : m y = wv) (hl : wv.length = W)
    (hlx : (m x).length ≤ W) : Ev (replaceC S x y) m (u (u m x wv) y []) (11 * W + 11) := by
  have e₁ := ev_clear' (S := S) (i := x) (L := W) hx m hlx
  have e₂ := ev_mv (S := S) (src := y) (dst := x) (L := W) (m := u m x []) (x := wv) hy hx (by omega)
    (by omega) (by omega) (by omega)
    (by rw [Function.update_of_ne (by omega)]; exact hc.w8)
    (by rw [Function.update_of_ne (by omega)]; exact hmy) (by simp) (by omega)
  rw [Function.update_idem] at e₂
  exact (EvQ.seq e₁ e₂).mono (by omega)

theorem correct_let {W : ℕ} {a b : Expr} {Ca Cb : List ℕ → ℕ → Cmd 10 S}
    (ha : Correct W a Ca) (hb : Correct W b Cb) : Correct W (.letE a b) (letC S Ca Cb) := by
  intro map env t m hg ht
  simp only [stack] at ht
  have hsb := stack_pos b
  have henv := hg.env_lt
  have hA := eval_lt_word W a env henv
  have g₁ := ha map env t m hg (by omega)
  have hg₁ : Good W map env (t + 1) (u m (11 + t) (wordOf W (eval W a env))) := hg.step
  have hg₁' : Good W (t :: map) (eval W a env :: env) (t + 1) (u m (11 + t) (wordOf W (eval W a env))) :=
    hg₁.cons (by omega) (by simp) hA
  have g₂ := hb (t :: map) (eval W a env :: env) (t + 1) _ hg₁' (by omega)
  have hBv := eval_lt_word W b (eval W a env :: env) hg₁'.env_lt
  set v := eval W b (eval W a env :: env) with hv
  set M := u (u m (11 + t) (wordOf W (eval W a env))) (11 + (t + 1)) (wordOf W v) with hM
  have hg₂ : Good W map env (t + 1 + 1) M := hg₁.step
  have e := ev_replace (S := S) (W := W) (x := 11 + t) (y := 11 + (t + 1)) (wv := wordOf W v) (m := M)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hg₂.clean (by simp [hM]) (by simp)
    (by simp [hM, Function.update_apply])
  have h₂ := hg.empty (t + 1) (by omega)
  have hmem : u (u M (11 + t) (wordOf W v)) (11 + (t + 1)) [] = u m (11 + t) (wordOf W (eval W (.letE a b) env)) := by
    simp only [hM, eval, ← hv]
    mem_eq'
  rw [hmem] at e
  have g₃ : Go (B W) (replaceC S (11 + t) (11 + (t + 1))) M _ _ :=
    go_routine e hg₂.small (by have := square_ge W; simp only [T]; omega)
  have hcost : ops W (.letE a b) env * T W = T W + ops W a env * T W + ops W b (eval W a env :: env) * T W := by
    simp only [ops]
    ring
  rw [hcost]
  refine (GoQ.seq g₁ (GoQ.seq g₂ g₃)).mono ?_
  have := square_ge W
  simp only [T] at *
  omega

/-! ### Loops: bound, accumulator, counter -/

/-- The memory at the guard of a loop. -/
def L2 (W : ℕ) (m : Mem) (t N a k : ℕ) : Mem :=
  u (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W a)) (11 + (t + 1 + 1)) (wordOf W k)

/-- The end of a loop body: count, then compute the guard. -/
def incCmpC (S : ℕ) [NeZero S] (kS nS : ℕ) : Cmd 10 S := .seq (incC S kS) (cmpC S kS nS)

theorem ev_incCmp {W k N kS nS : ℕ} {m : Mem} (hS : 11 ≤ S) (hk : kS < S) (hn : nS < S) (hk11 : 11 ≤ kS)
    (hn11 : 11 ≤ nS) (hne : kS ≠ nS) (hc : Clean W m) (hmk : m kS = wordOf W k) (hmn : m nS = wordOf W N)
    (hlt : k < N) (hN : N < 2 ^ W) :
    EvQ (incCmpC S kS nS) m (u m kS (wordOf W (k + 1))) (54 * W + 71) fun r => r 0 = decide (k + 1 < N) := by
  have e₁ := ev_inc (S := S) (W := W) (k := k) (i := kS) hk hS (by omega) hc.w1 hmk (by omega)
  have e₂ := ev_cmp (S := S) (W := W) (x := kS) (y := nS) (a := k + 1) (b := N) (m := u m kS (wordOf W (k + 1)))
    hS hk hn hk11 hn11 (hc.high hk11 _) (by simp)
    (by rw [Function.update_of_ne (by omega)]; exact hmn) (by omega) hN
  exact (EvQ.seq e₁ e₂).mono (by omega)

/-- Before the loop: the counter is the word of zero, and the guard is computed. -/
def setupC (S : ℕ) [NeZero S] (t : ℕ) : Cmd 10 S :=
  .seq (copyC S 10 (11 + (t + 1 + 1))) (cmpC S (11 + (t + 1 + 1)) (11 + t))

/-- After the loop: the accumulator goes to the slot `t`. -/
def finishC (S : ℕ) [NeZero S] (t : ℕ) : Cmd 10 S :=
  .seq (clearC S (11 + t)) (.seq (clearC S (11 + (t + 1 + 1))) (mvC S (11 + (t + 1)) (11 + t)))

/-- The loop shape: the initial accumulator, the guard, the body, and the final clean-up. -/
def loop2C (S : ℕ) [NeZero S] (Cinit Bd : Cmd 10 S) (t : ℕ) : Cmd 10 S :=
  .seq Cinit (.seq (.seq (setupC S t) (.while 0 (.seq Bd (incCmpC S (11 + (t + 1 + 1)) (11 + t))))) (finishC S t))

theorem go_loop2 {W t N ti t' : ℕ} {v β φ : ℕ → ℕ} {Cinit Bd : Cmd 10 S} {map env : List ℕ} {m : Mem}
    (hg : Good W map env t m) (ht : 11 + t + 3 ≤ S) (hN : N < 2 ^ W) (hv : ∀ k ≤ N, v k < 2 ^ W)
    (hinit : Go (B W) Cinit (u m (11 + t) (wordOf W N))
      (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (v 0))) ti)
    (hbody : ∀ k < N, Go (B W) Bd (L2 W m t N (v k) k) (L2 W m t N (v (k + 1)) k) (β k))
    (hφ : ∀ k < N, φ k * T W + (β k + (54 * W + 71)) + 1 ≤ φ (k + 1) * T W)
    (hfinal : ti + (53 * W + 68) + (13 * W + 14) + φ N * T W + 1 ≤ t' + φ 0 * T W) :
    Go (B W) (loop2C S Cinit Bd t) (u m (11 + t) (wordOf W N)) (u m (11 + t) (wordOf W (v N))) t' := by
  have hsq := square_ge W
  have hBig : 100 * W + 100 ≤ T W := by simp only [T]; omega
  have hgL : ∀ a k, a < 2 ^ W → k < 2 ^ W → Good W map env (t + 1 + 1 + 1) (L2 W m t N a k) := fun a k _ _ =>
    (hg.step.step.step : Good W map env (t + 1 + 1 + 1) (L2 W m t N a k))
  have hmn : ∀ a k, L2 W m t N a k (11 + t) = wordOf W N := fun a k => by
    simp only [L2]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hmk : ∀ a k, L2 W m t N a k (11 + (t + 1 + 1)) = wordOf W k := fun a k => by
    simp only [L2, Function.update_self]
  have hma : ∀ a k, L2 W m t N a k (11 + (t + 1)) = wordOf W a := fun a k => by
    simp only [L2]
    rw [Function.update_of_ne (by omega), Function.update_self]
  have h₁ := hg.empty (t + 1) (by omega)
  have h₂ := hg.empty (t + 1 + 1) (by omega)
  -- the setup
  have gs : GoQ (B W) (setupC S t) (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (v 0)))
      (L2 W m t N (v 0) 0) (53 * W + 68) fun r => r 0 = decide (0 < N) := by
    have hg₂ : Good W map env (t + 1 + 1) (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (v 0))) :=
      hg.step.step
    have e₁ : Ev (copyC S 10 (11 + (t + 1 + 1)))
        (u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (v 0))) (L2 W m t N (v 0) 0) (7 * W + 5) :=
      ev_copy' (S := S) (src := 10) (dst := 11 + (t + 1 + 1)) (L := W)
      (m := u (u m (11 + t) (wordOf W N)) (11 + (t + 1)) (wordOf W (v 0))) (x := wordOf W 0)
      (by omega) (by omega) (by omega) (by omega) (by norm_num) (by omega) hg₂.clean.w8
      (by rw [hg₂.clean.ruler, wordOf_zero]) (hg₂.empty _ le_rfl) (by simp)
    have e₂ := ev_cmp (S := S) (W := W) (x := 11 + (t + 1 + 1)) (y := 11 + t) (a := 0) (b := N)
      (m := L2 W m t N (v 0) 0) (by omega) (by omega) (by omega) (by omega) (by omega)
      (hgL _ _ (hv 0 (by omega)) (by positivity)).clean (hmk _ _) (hmn _ _) (by positivity) hN
    exact go_routine ((EvQ.seq e₁ e₂).mono (by omega)) hg₂.small (by omega)
  -- the body
  have gb : ∀ k < N, GoQ (B W) (.seq Bd (incCmpC S (11 + (t + 1 + 1)) (11 + t))) (L2 W m t N (v k) k)
      (L2 W m t N (v (k + 1)) (k + 1)) (β k + (54 * W + 71)) fun r => r 0 = decide (k + 1 < N) := by
    intro k hk
    have hgg := hgL (v (k + 1)) k (hv _ (by omega)) (by omega)
    have e := ev_incCmp (S := S) (W := W) (k := k) (N := N) (kS := 11 + (t + 1 + 1)) (nS := 11 + t)
      (m := L2 W m t N (v (k + 1)) k) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hgg.clean (hmk _ _) (hmn _ _) hk hN
    have hmem : u (L2 W m t N (v (k + 1)) k) (11 + (t + 1 + 1)) (wordOf W (k + 1)) =
        L2 W m t N (v (k + 1)) (k + 1) := by
      simp only [L2, Function.update_idem]
    rw [hmem] at e
    exact GoQ.seq (hbody k hk) (go_routine e hgg.small (by omega))
  have hsN := (hgL (v N) N (hv N le_rfl) hN).small
  have hsB : ∀ i, (L2 W m t N (v N) N i).length ≤ B W := fun i =>
    (hsN i).trans (by simp only [B]; omega)
  have hmono := phi_mono (Φ := fun k => φ k * T W) (τ := fun k => β k + (54 * W + 71)) (N := N) hφ
  have gloop := go_for (t := 53 * W + 68 + φ N * T W + 1 - φ 0 * T W) (fun k => L2 W m t N (v k) k) N
    (fun k => φ k * T W) (fun k => β k + (54 * W + 71)) gs gb hφ hsB (by simp only at *; omega)
  -- the clean-up
  have gf : Go (B W) (finishC S t) (L2 W m t N (v N) N) (u m (11 + t) (wordOf W (v N))) (13 * W + 14) := by
    set M := L2 W m t N (v N) N with hM
    have e₁ := ev_clear' (S := S) (i := 11 + t) (L := W) (by omega) M (by rw [hM, hmn]; simp)
    have e₂ := ev_clear' (S := S) (i := 11 + (t + 1 + 1)) (L := W) (by omega) (u M (11 + t) [])
      (by rw [Function.update_of_ne (by omega), hM, hmk]; simp)
    set M₂ := u (u M (11 + t) []) (11 + (t + 1 + 1)) [] with hM₂
    have hc₂ : Clean W M₂ := ((hgL (v N) N (hv N le_rfl) hN).clean.high (by omega) _).high (by omega) _
    have e₃ := ev_mv (S := S) (src := 11 + (t + 1)) (dst := 11 + t) (L := W) (m := M₂) (x := wordOf W (v N))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hc₂.w8
      (by rw [hM₂, Function.update_of_ne (by omega), Function.update_of_ne (by omega), hM, hma])
      (by rw [hM₂, Function.update_of_ne (by omega)]; simp) (by simp)
    have hmem : u (u M₂ (11 + t) (wordOf W (v N))) (11 + (t + 1)) [] = u m (11 + t) (wordOf W (v N)) := by
      simp only [hM₂, hM, L2]
      mem_eq'
    rw [hmem] at e₃
    exact go_routine (EvQ.seq e₁ (EvQ.seq e₂ e₃)) hsN (by omega) |>.mono (by omega)
  refine (GoQ.seq hinit (GoQ.seq gloop gf)).mono ?_
  simp only at *
  omega

end TransposeBase.Machine
