module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Diagonals of locally finite type morphisms of formal spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType

/-- The relative diagonal of a locally of finite type morphism of functors of
points on schemes is locally of finite type. -/
instance diagonal {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [LocallyOfFiniteType f] : LocallyOfFiniteType (pullback.diagonal f) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType
