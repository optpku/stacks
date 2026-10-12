/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Composition of integral and finite morphisms of algebraic spaces

The composition of integral morphisms of algebraic spaces is integral, and the
composition of finite morphisms of algebraic spaces is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Integral morphisms of algebraic spaces are stable under composition. -/
instance isIntegralHom_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsIntegralHom S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of two integral morphisms of algebraic spaces is integral. -/
instance isIntegralHom_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) :=
  MorphismProperty.comp_mem (@IsIntegralHom S) f g inferInstance inferInstance

/-- Finite morphisms of algebraic spaces are stable under composition. -/
instance isFinite_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@IsFinite S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of two finite morphisms of algebraic spaces is finite. -/
instance isFinite_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g] :
    IsFinite (f ≫ g) :=
  MorphismProperty.comp_mem (@IsFinite S) f g inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace
