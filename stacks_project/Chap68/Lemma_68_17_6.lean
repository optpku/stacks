/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Composition of relative property (β), decent, and reasonable morphisms

Having property (β), being decent, or being reasonable is preserved under
compositions of morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.17.6 (1): Having property (β) is preserved under compositions. -/
@[stacks 03L1]
instance propertyBeta_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@PropertyBeta S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of morphisms of algebraic spaces with property (β) has property (β). -/
instance propertyBeta_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [PropertyBeta f] [PropertyBeta g] :
    PropertyBeta (f ≫ g) := sorry

/-- Lemma 68.17.6 (2): Being decent is preserved under compositions. -/
@[stacks 03L1]
instance decent_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Decent S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of decent morphisms of algebraic spaces is decent. -/
instance decent_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Decent f] [Decent g] :
    Decent (f ≫ g) := sorry

/-- Lemma 68.17.6 (3): Being reasonable is preserved under compositions. -/
@[stacks 03L1]
instance reasonable_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Reasonable S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composition of reasonable morphisms of algebraic spaces is reasonable. -/
instance reasonable_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Reasonable f] [Reasonable g] :
    Reasonable (f ≫ g) := sorry

end AlgebraicGeometry.AlgebraicSpace
