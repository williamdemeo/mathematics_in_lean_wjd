import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h'
      exact Or.inl h'
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h'
      exact Or.inr h'

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt 0 x
  case inl h =>
    rw [abs_of_nonneg h]
  case inr h =>
    rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  match le_or_gt 0 x with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      apply le_trans (neg_nonpos.mpr h) h
    | Or.inr h =>
      rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  cases le_or_gt 0 (x + y)
  case inl h =>
    rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  case inr h =>
    rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · match le_or_gt 0 y with
      | Or.inl h' =>
        rw [abs_of_nonneg h']
        intro h''
        exact Or.inl h''
      | Or.inr h' =>
        rw [abs_of_neg h']
        intro h''
        exact Or.inr h''
  · intro h
    cases h
    case inl h =>
      apply lt_of_lt_of_le h (le_abs_self y)
    case inr h =>
      apply lt_of_lt_of_le h (neg_le_abs_self y)

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    match le_or_gt 0 x with
      | Or.inl h' =>
        rw [abs_of_nonneg h'] at h
        exact ⟨by linarith [h], h⟩
      | Or.inr h₁ =>
        have h₂ : 0 < y := lt_of_le_of_lt (abs_nonneg x) h
        rw [abs_of_neg h₁] at h
        exact ⟨by linarith [h], lt_trans h₁ h₂⟩
  · intro h
    match le_or_gt 0 x with
      | Or.inl h' =>
        rw [abs_of_nonneg h']
        exact h.2
      | Or.inr h' =>
        rw [abs_of_neg h']
        linarith [h.1]

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, _ | _⟩; repeat linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have  h₁ : (x - 1) * (x + 1) = 0 := by linarith [h]
  have   h₂ : x - 1 = 0 ∨ x + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h₁
  rcases h₂
  · apply Or.inl (by linarith)
  . apply Or.inr (by linarith)

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ : (x - y) * (x + y) = 0 := by linarith [h]
  have h₂ : x - y = 0 ∨ x + y = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h₁
  rcases h₂
  · apply Or.inl (by linarith)
  . apply Or.inr (by linarith)
section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have  h₀ : x ^ 2 - 1 = 0 := by rw [h]; simp
  have  h₁ : (x - 1) * (x + 1) = 0 := by
    calc
      (x - 1) * (x + 1) = x ^ 2 + x - x - 1 := by ring
                      _ = x ^ 2 - 1 := by ring
                      _ = 0 := by rw [h₀]
  have h1 : x - 1 = 0 → x = 1 := by
    intro h
    calc
      x = x - 1 + 1 := by ring
      _ = 1 := by rw [h, zero_add]
  have h2 : x + 1 = 0 → x = -1 := by
    intro h
    calc
      x = x + 1 - 1 := by ring
      _ = -1 := by rw [h, zero_sub]
  have   h₂ : x - 1 = 0 ∨ x + 1 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h₁
  rcases h₂ with h' | h'
  · apply Or.inl (h1 h')
  · apply Or.inr (h2 h')


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ : (x - y) * (x + y) = 0 := by
    calc
      (x - y) * (x + y) = x ^ 2 + x*y - y*x - y ^ 2 := by ring
                      _ = x ^ 2 + x*y - x*y - y ^ 2 := by ring
                      _ = x ^ 2 - y ^ 2 := by ring
                      _ = 0 := by rw [h]; ring
  have h1 : x - y = 0 → x = y := by
    intro h
    calc
      x = x - y + y := by ring
      _ = y := by rw [h, zero_add]
  have h2 : x + y = 0 → x = -y := by
    intro h
    calc
      x = x + y - y := by ring
      _ = -y := by rw [h, zero_sub]
  have h₂ : x - y = 0 ∨ x + y = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h₁
  rcases h₂ with h' | h'
  · apply Or.inl (h1 h')
  . apply Or.inr (h2 h')

end

-- TODO: Assume R is a Ring instead of an CommRing and prove the first of the
-- two theorems above (i.e., without commutativity of multiplication).

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h₁ : P
    · exact Or.inr (h h₁)
    . exact Or.inl h₁
  · intro h
    rcases h with _ | h₂
    · exact fun _ => by contradiction
    . exact fun _ => h₂
