import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  repeat apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  repeat apply h

theorem le_min_le_left (h : a ≤ b) : min a c ≤ b := by
  apply le_trans (min_le_left _ _) h

theorem le_min_le_right (h : c ≤ b) : min a c ≤ b := by
  apply le_trans (min_le_right _ _) h


example : min (min a b) c = min a (min b c) := by
  have v : min (min a b) c ≤ b := by
    apply le_min_le_left (min a b) b c (min_le_right a b)
  have h₁ : min (min a b) c ≤ min a (min b c) := by
    apply le_min (le_min_le_left _ _ _ (min_le_left _ _))
                 (le_min v (min_le_right _ _))
  have q : min a (min b c) ≤ min a b := by
    apply le_min (min_le_left a _)
                 (le_min_le_right _ _ _ (min_le_left _ _))
  have r : min a (min b c) ≤ c := by
    apply le_trans (min_le_right _ _) (min_le_right _ _)
  have h₂ : min a (min b c) ≤ min (min a b) c := by
    apply le_min q r
  apply le_antisymm
  apply h₁
  apply h₂

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h₁ : min a b + c ≤ a + c := by
    apply add_le_add (min_le_left a b) (le_refl c)

  have h₂ : min a b + c ≤ b + c := by
    apply add_le_add (min_le_right a b) (le_refl c)
  apply le_min h₁ h₂

#check add_neg_cancel_right

theorem le_sub_const : a ≤ b → a - c ≤ b - c := by
  intro h
  apply sub_le_sub h (le_refl c)

theorem le_add_const : a ≤ b → a + c ≤ b + c := by
  intro h
  apply add_le_add h (le_refl c)

theorem le_add_const_cancel : a + c ≤ b + c → a ≤ b := by
  intro h
  have h₃ : a + c + - c ≤ b + c + - c := by
    apply le_add_const (a + c) (b + c) (-c) h
  calc
    a = a + c + -c := by ring
    _ ≤ b + c + -c := by apply h₃
    _ = b := by ring

theorem le_add_const_iff : a ≤ b ↔ a + c ≤ b + c := by
  exact ⟨ le_add_const a b c , le_add_const_cancel a b c ⟩

example : min a b + c = min (a + c) (b + c) := by
  have h₁ : min a b + c ≤ min (a + c) (b + c) := by apply aux

  have h₂ : min (a + c) (b + c) ≤ min a b + c := by
    calc
    min (a + c) (b + c) = min (a + c) (b + c) + c + - c := by
      rw [add_neg_cancel_right (min (a + c) (b + c)) c]
    _ = min (a + c) (b + c) + (c + - c) := by rw [add_assoc]
    _ = min (a + c) (b + c) + (- c + c) := by rw [add_comm c]
    _ = min (a + c) (b + c) + - c + c := by rw [add_assoc]
    _ ≤ min (a + c + - c) (b + c + - c) + c := by
      apply le_add_const (min (a + c) (b + c) + - c)
                         (min (a + c + - c) (b + c + - c)) c
                         (aux (a + c) (b + c) (- c))
    _ = min a b + c := by
      repeat rw [add_assoc, add_neg_self, add_zero]

  apply le_antisymm
  apply h₁
  apply h₂

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h : |a| ≤ |a - b| + |b| := by
    calc
      |a| = |a - b + b| := by rw [sub_add_cancel]
      _ ≤ |a - b| + |b| := by apply abs_add (a - b) b
  calc
    |a| - |b| ≤ |a - b| + |b| - |b| := by
      apply le_sub_const |a| (|a - b| + |b|) |b| h
    _ = |a - b| := by ring
end
#check sub_add_cancel
section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  repeat apply dvd_add
  apply dvd_mul_of_dvd_right
  apply dvd_mul_right
  apply dvd_mul_left
  apply dvd_mul_of_dvd_right h

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.gcd_comm m n
end
