/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of finite type morphisms of algebraic spaces

The composition of a pair of finite type morphisms of algebraic spaces is of
finite type, and the same holds for morphisms locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.23.2 (1): The composition of finite type morphisms of algebraic
spaces is of finite type. -/
@[stacks 03XG]
instance finiteType_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FiniteType S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of finite type morphisms of algebraic spaces is of finite
type. -/
instance finiteType_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) := sorry

/-- Lemma 67.23.2 (2): The composition of locally of finite type morphisms of
algebraic spaces is locally of finite type. -/
@[stacks 03XG]
instance locallyOfFiniteType_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of locally of finite type morphisms of algebraic spaces is
locally of finite type. -/
instance locallyOfFiniteType_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    LocallyOfFiniteType (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
