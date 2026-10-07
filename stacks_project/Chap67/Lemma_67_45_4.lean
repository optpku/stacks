module

public import stacks_project.Chap67.Definition_67_45_2_Integral
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of integral and finite morphisms of algebraic spaces

The composition of integral morphisms of algebraic spaces is integral, and the
composition of finite morphisms of algebraic spaces is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.45.4 (1): The composition of integral morphisms of algebraic spaces is
integral. -/
@[stacks 03ZR]
instance isIntegralHom_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsIntegralHom S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of integral morphisms of algebraic spaces is integral. -/
instance isIntegralHom_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) := sorry

/-- Lemma 67.45.4 (2): The composition of finite morphisms of algebraic spaces is
finite. -/
@[stacks 03ZR]
instance isFinite_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsFinite S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of finite morphisms of algebraic spaces is finite. -/
instance isFinite_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g] :
    IsFinite (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
