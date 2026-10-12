/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of finite presentation morphisms of algebraic spaces

The composition of a pair of finite presentation morphisms of algebraic spaces
is of finite presentation, and the same holds for morphisms locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.28.2 (1): The composition of finite presentation morphisms of
algebraic spaces is of finite presentation. -/
@[stacks 03XQ]
instance finitePresentation_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FinitePresentation S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of finite presentation morphisms of algebraic spaces is of
finite presentation. -/
instance finitePresentation_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FinitePresentation f] [FinitePresentation g] :
    FinitePresentation (f ≫ g) := sorry

/-- Lemma 67.28.2 (2): The composition of locally of finite presentation
morphisms of algebraic spaces is locally of finite presentation. -/
@[stacks 03XQ]
instance locallyOfFinitePresentation_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)) :=
    sorry

/-- The composition of locally of finite presentation morphisms of algebraic
spaces is locally of finite presentation. -/
instance locallyOfFinitePresentation_comp {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
