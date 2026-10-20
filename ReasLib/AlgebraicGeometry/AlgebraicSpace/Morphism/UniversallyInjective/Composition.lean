module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of universally injective morphisms of algebraic spaces

The composition of universally injective morphisms of algebraic spaces is
universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universally injective morphisms of algebraic spaces are stable under composition. -/
instance universallyInjective_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversallyInjective S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universally injective morphisms of algebraic spaces is
universally injective. -/
instance universallyInjective_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyInjective f] [UniversallyInjective g] :
    UniversallyInjective (f ≫ g) :=
  MorphismProperty.comp_mem (@UniversallyInjective S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
