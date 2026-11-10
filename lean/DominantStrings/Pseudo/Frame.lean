import DominantStrings.Pseudo.Prog

/-!
# The frame of the program, and the specifications of programs for weights and word functions
-/

namespace DominantStrings.Pseudo

open Finset TransposeBase.Pseudo TransposeBase.Pseudo.Leaf

/-- The values of the frame of the program. -/
structure Frm where
  c : ℕ
  bk : ℕ
  sc : ℕ
  pT : ℕ
  hT : ℕ
  tT : ℕ
  fw : ℕ
  v : ℕ
  m : ℕ
  rest : List ℕ

/-- The frame as a list. -/
def Frm.list (f : Frm) : List ℕ := f.c :: f.bk :: f.sc :: f.pT :: f.hT :: f.tT :: f.fw :: f.v :: f.m :: f.rest

/-- The frame has the index `g` in the environment. -/
def Frm.At (f : Frm) (env : List ℕ) (g : ℕ) : Prop := ∃ pre : List ℕ, pre.length = g ∧ env = pre ++ f.list

theorem Frm.At.up {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) (x : ℕ) : f.At (x :: env) (g + 1) := by
  obtain ⟨pre, h1, h2⟩ := h
  exact ⟨x :: pre, by simp [h1], by simp [h2]⟩

theorem Frm.At.getD {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) (i : ℕ) :
    env.getD (g + i) 0 = f.list.getD i 0 := by
  obtain ⟨pre, h1, rfl⟩ := h
  subst h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem Frm.At.c {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD g 0 = f.c := h.getD 0
theorem Frm.At.bk {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD (g + 1) 0 = f.bk := h.getD 1
theorem Frm.At.sc {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD (g + 2) 0 = f.sc := h.getD 2
theorem Frm.At.pT {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD (g + 3) 0 = f.pT := h.getD 3
theorem Frm.At.hT {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD (g + 4) 0 = f.hT := h.getD 4
theorem Frm.At.tT {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD (g + 5) 0 = f.tT := h.getD 5
theorem Frm.At.fw {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD (g + 6) 0 = f.fw := h.getD 6
theorem Frm.At.v {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD (g + 7) 0 = f.v := h.getD 7
theorem Frm.At.m {f : Frm} {env : List ℕ} {g : ℕ} (h : f.At env g) : env.getD (g + 8) 0 = f.m := h.getD 8

/-- `wt` is a program for the weights `w` on the words below `K`, with at most `C` operations. -/
def WtSpec (W : ℕ) (f : Frm) (K : ℕ) (wt : ℕ → ℕ → ℕ → Expr) (w : ℕ → ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ {g ix iy x y : ℕ} {env : List ℕ}, f.At env g → env.getD ix 0 = x → env.getD iy 0 = y → x < K → y < K →
    Run W (wt g ix iy) env (w x y) C

/-- `word` is a program for the word functions `F` of the level with weights `w`. The numbers `B y` of a word are the fields of one
number `Z`. -/
def WordSpec (W : ℕ) (f : Frm) (K : ℕ) (word : ℕ → ℕ → ℕ → Expr) (w : ℕ → ℕ → ℕ)
    (F : ℕ → (ℕ → ℕ) → ℤ) (C : ℕ) : Prop :=
  ∀ {g ix iZ x Z : ℕ} {env : List ℕ}, f.At env g → env.getD ix 0 = x → env.getD iZ 0 = Z → x < K →
    Z < 2 ^ (∑ y ∈ range K, w x y) →
    RunZ W (word g ix iZ) env (F x (viewL K (w x) Z)) C

/-- The level of the step with the bits from `base` on. -/
def stepLev (K' base sc c : ℕ) (w : ℕ → ℕ → ℕ) : Lev :=
  ⟨K', w, c / 2 ^ base % 2 ^ K' ^ 4, dirOf K' w sc (c / 2 ^ base % 2 ^ K' ^ 4), sc⟩

end DominantStrings.Pseudo
