module

public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Composition of open morphisms of algebraic spaces

The composition of a pair of open morphisms of algebraic spaces is open, and
the composition of a pair of universally open morphisms of algebraic spaces is
universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.6.4 (1): The composition of a pair of open morphisms of algebraic spaces
is open. -/
@[stacks 03Z4]
instance open_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Open S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of open morphisms of algebraic spaces is open. -/
instance open_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Open f] [Open g] :
    Open (f ≫ g) := sorry

/-- Lemma 67.6.4 (2): The composition of a pair of universally open morphisms of
algebraic spaces is universally open. -/
@[stacks 03Z4]
instance universallyOpen_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of universally open morphisms of algebraic spaces is
universally open. -/
instance universallyOpen_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyOpen f] [UniversallyOpen g] :
    UniversallyOpen (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
