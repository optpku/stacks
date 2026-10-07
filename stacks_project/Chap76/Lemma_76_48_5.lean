module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Composition of local complete intersection morphisms of algebraic spaces

A composition of local complete intersection morphisms of algebraic spaces is
a local complete intersection morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.48.5: A composition of local complete intersection morphisms is
a local complete intersection morphism. -/
@[stacks 06C8]
instance IsLocalCompleteIntersection.comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsLocalCompleteIntersection f] [IsLocalCompleteIntersection g] :
    IsLocalCompleteIntersection (f ≫ g) :=
  sorry

/-- Local complete intersection morphisms of algebraic spaces are stable under
composition. -/
instance IsLocalCompleteIntersection.instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsLocalCompleteIntersection S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
