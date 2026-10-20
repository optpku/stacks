module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.RelativeFunction

/-! Compatibility facade for the canonical public owner. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f],
    (Points B → ℤ) → Points X → ℤ)
