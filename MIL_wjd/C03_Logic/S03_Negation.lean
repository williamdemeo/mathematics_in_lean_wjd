import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : a ≤ f x := fnlba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro h
  rcases h with ⟨a, ha⟩
  have h' : a < (a + 1) := by linarith
  have : (a + 1) ≤ a := ha (a + 1)
  apply lt_irrefl (a + 1) (lt_of_le_of_lt this h')

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  have : ¬ a ≥ b := by
    intro h₀
    have h₁ : f b ≤ f a := h h₀
    linarith
  apply lt_of_not_ge this

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro hmono
  have : f a ≤ f b := hmono h
  apply (not_le_of_gt h') this

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun _ : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro _ _ _
    apply le_refl
  have h₁ : f 1 ≤ f 0 := le_refl _
  have h₂ : (0 : ℝ) < 1 := by simp
  apply (not_le_of_gt h₂) (h monof h₁)

#check le_of_not_gt -- ¬a > b → a ≤ b
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  have h₁ : ¬ x > 0 := by
    intro xg0
    let ε := x / 2
    have h₂ : x / 2 ≤ x := by linarith
    have h₃ : ε ≤ x := by apply h₂
    have h₄ : x / 2 > 0 := by linarith
    have h₅ : ε > 0 := by apply h₄
    have h₇ : ¬ x < ε := by apply not_lt_of_ge h₃
    apply h₇ (h ε h₅)
  apply le_of_not_gt h₁

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h ⟨x , Px⟩

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro xPx
  rcases xPx with ⟨x, Px⟩
  apply (h x) Px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h₁
  rcases h with ⟨x, nPx⟩
  apply nPx (h₁ x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h
  exact h'

example (h : Q) : ¬¬Q := by
  intro h'
  apply h' h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  have h'' : FnHasUb f := by
    use a
    intro x
    by_contra h'''
    apply h'
    use x
    apply lt_of_not_ge h'''
  apply h h''

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
