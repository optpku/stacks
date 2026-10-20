module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Composition

/-!
# Composition of local complete intersection morphisms of algebraic spaces

Local complete intersection morphisms of algebraic spaces are stable under
composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Local complete intersection morphisms of algebraic spaces are stable under
composition. -/
instance IsLocalCompleteIntersection.instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S)) where
  comp_mem f g hf hg := by
    sorry

/-- A composition of local complete intersection morphisms of algebraic spaces
is a local complete intersection morphism. -/
instance IsLocalCompleteIntersection.comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocalCompleteIntersection f] [IsLocalCompleteIntersection g] :
    IsLocalCompleteIntersection (f ≫ g) :=
  MorphismProperty.comp_mem
    (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S))
    f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
