/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_9_2_Closed

/-!
# Composition of closed morphisms of algebraic spaces

The composition of a pair of closed morphisms of algebraic spaces is closed,
and the composition of a pair of universally closed morphisms of algebraic
spaces is universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.9.4 (1): The composition of a pair of closed morphisms of algebraic spaces
is closed. -/
@[stacks 03IU]
instance closed_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Closed S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of closed morphisms of algebraic spaces is closed. -/
instance closed_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Closed f] [Closed g] :
    Closed (f ≫ g) := sorry

/-- Lemma 67.9.4 (2): The composition of a pair of universally closed morphisms of
algebraic spaces is universally closed. -/
@[stacks 03IU]
instance universallyClosed_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversallyClosed S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universally closed morphisms of algebraic spaces is
universally closed. -/
instance universallyClosed_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed f] [UniversallyClosed g] :
    UniversallyClosed (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
