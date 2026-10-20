module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Equalizers

This file provides a proposition expressing that a morphism and its equalizing equation exhibit an
equalizer of a parallel pair.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D]
variable {A B C : D}

/-- A morphism `f : A ⟶ B` is an equalizer of `g₁ g₂ : B ⟶ C` with equalizing equation
`h` when its associated fork is limiting. -/
def IsEqualizer (f : A ⟶ B) (g₁ g₂ : B ⟶ C) (h : f ≫ g₁ = f ≫ g₂) : Prop :=
  Nonempty (IsLimit (Fork.ofι f h))

end CategoryTheory.Limits
