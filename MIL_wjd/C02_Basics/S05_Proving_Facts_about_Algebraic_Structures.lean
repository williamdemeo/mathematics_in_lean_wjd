import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  have h₁ : x ⊓ y ≤ y ⊓ x := by apply le_inf; apply inf_le_right; apply inf_le_left
  have h₂ : y ⊓ x ≤ x ⊓ y := by apply le_inf; apply inf_le_right; apply inf_le_left
  apply le_antisymm h₁ h₂

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm LE GE
  where
  LE : x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z) := by
    apply le_inf
    apply le_trans inf_le_left inf_le_left
    apply le_inf
    apply le_trans inf_le_left inf_le_right
    apply inf_le_right
  GE : x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z := by
    apply le_inf
    apply le_inf inf_le_left (le_trans inf_le_right inf_le_left)
    apply le_trans inf_le_right inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply sup_comm

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply sup_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm inf_le_left (le_inf (le_refl x) (le_sup_left))
#check sup_inf_self
theorem absorb2 : x ⊔ (x ⊓ y) = x := by
  apply le_antisymm (sup_le (le_refl x) inf_le_left) (le_sup_left)
end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := Eq.symm (Eq.trans h₁ h₂)
  where
    h₁ : (a ⊔ b) ⊓ (a ⊔ c) = a ⊔ ((a ⊔ b) ⊓ c) := by rw [h, inf_comm, absorb1 a b]
    h₂ : a ⊔ ((a ⊔ b) ⊓ c) = a ⊔ (b ⊓ c) := by
      rw [inf_comm, h c a b, inf_comm, inf_comm c b, ←sup_assoc, absorb2 a c]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := Eq.symm (Eq.trans h₁ h₂)
  where
    h₁ : a ⊓ b ⊔ a ⊓ c = a ⊓ ((a ⊓ b) ⊔ c) := by rw [h, sup_comm, absorb2 a b]
    h₂ : a ⊓ ((a ⊓ b) ⊔ c) = a ⊓ (b ⊔ c) := by
      rw [sup_comm, h c a b, sup_comm, sup_comm b c, ←inf_assoc, absorb1 a c]
end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  calc
    0 = a - a := by rw [sub_self]
    _ ≤ b - a := sub_le_sub_right h a

theorem ge_zero_ge (h: b - a ≥ 0) : a ≤ b := by
  calc
    a = a + 0 := by rw [add_zero]
    _ ≤ a + (b - a) := add_le_add_left h a
    _ = b := by simp

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₁ : (b - a) * c ≥ 0 := mul_nonneg (sub_nonneg_of_le h) h'
  have h₂ : b * c - a * c ≥ 0 := by
    rw [←sub_mul]
    exact h₁
  exact ge_zero_ge (a * c) (b * c) h₂
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h₁ : dist x x ≤ dist x y + dist y x := dist_triangle x y x
  have h₂ : 0 ≤ dist x y + dist y x := by
    rw [←dist_self x]
    exact h₁
  have h₃ : 0 ≤ 2 * dist x y := by
    calc
      0 ≤ dist x y + dist y x := h₂
      _ = dist x y + dist x y := by rw [dist_comm y x]
      _ = 2 * dist x y := by rw [two_mul]
  linarith

end
