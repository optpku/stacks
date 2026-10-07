module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap101.Definition_101_9_1_Affine

/-!
# Composition of affine morphisms of algebraic stacks

The composition of a pair of affine morphisms of algebraic stacks is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Affine

/-- Lemma 101.9.3: compositions of affine morphisms of algebraic stacks are
affine. -/
@[stacks 0CHS]
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Affine f] [Affine g] : Affine (f ≫ g) := sorry

/-- Affine 1-morphisms of groupoid fibrations over `S` are stable under
composition as a morphism property. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Affine S : MorphismProperty (GroupoidsOver S)) := sorry

end Affine

end AlgebraicGeometry.Groupoids.Hom
