module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FiniteDimensionalPredeformations

/-! # Finite-dimensional tangent and infinitesimal automorphism spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupoidsOver.HasFiniteDimensionalPredeformations :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S], GroupoidsOver S → Prop)
