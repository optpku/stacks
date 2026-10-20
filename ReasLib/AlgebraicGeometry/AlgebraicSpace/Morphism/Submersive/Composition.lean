module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of submersive morphisms of algebraic spaces

Submersive morphisms of algebraic spaces are stable under composition, as are
universally submersive morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Submersive morphisms of algebraic spaces are stable under composition. -/
instance submersive_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Submersive S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of submersive morphisms of algebraic spaces is submersive. -/
instance submersive_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Submersive f] [Submersive g] :
    Submersive (f ≫ g) :=
  MorphismProperty.comp_mem (@Submersive S) f g inferInstance inferInstance

/-- Universally submersive morphisms of algebraic spaces are stable under composition. -/
instance universallySubmersive_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversallySubmersive S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universally submersive morphisms of algebraic spaces is
universally submersive. -/
instance universallySubmersive_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallySubmersive f] [UniversallySubmersive g] :
    UniversallySubmersive (f ≫ g) :=
  MorphismProperty.comp_mem (@UniversallySubmersive S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
