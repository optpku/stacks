module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of relative property (β), decent, and reasonable morphisms

Having property (β), being decent, or being reasonable is preserved under
compositions of morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Property (β) of morphisms of algebraic spaces is stable under composition. -/
instance propertyBeta_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@PropertyBeta S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of morphisms of algebraic spaces with property (β) has property (β). -/
instance propertyBeta_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [PropertyBeta f] [PropertyBeta g] :
    PropertyBeta (f ≫ g) :=
  MorphismProperty.comp_mem (@PropertyBeta S) f g inferInstance inferInstance

/-- Decency of morphisms of algebraic spaces is stable under composition. -/
instance decent_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Decent S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of decent morphisms of algebraic spaces is decent. -/
instance decent_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Decent f] [Decent g] :
    Decent (f ≫ g) :=
  MorphismProperty.comp_mem (@Decent S) f g inferInstance inferInstance

/-- Reasonableness of morphisms of algebraic spaces is stable under composition. -/
instance reasonable_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Reasonable S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of reasonable morphisms of algebraic spaces is reasonable. -/
instance reasonable_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Reasonable f] [Reasonable g] :
    Reasonable (f ≫ g) :=
  MorphismProperty.comp_mem (@Reasonable S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
