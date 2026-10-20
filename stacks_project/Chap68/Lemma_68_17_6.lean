module

public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Composition
import StacksCheckRecall

/-!
# Composition of relative property (β), decent, and reasonable morphisms

Having property (β), being decent, or being reasonable is preserved under
compositions of morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.17.6 (1): Having property (β) is preserved under compositions. -/
@[stacks 03L1]
#check (AlgebraicGeometry.AlgebraicSpace.propertyBeta_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@PropertyBeta S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.propertyBeta_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y ⟶ Z) [PropertyBeta f] [PropertyBeta g],
      PropertyBeta (f ≫ g))

/- Lemma 68.17.6 (2): Being decent is preserved under compositions. -/
@[stacks 03L1]
#check (AlgebraicGeometry.AlgebraicSpace.decent_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@Decent S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.decent_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y ⟶ Z) [Decent f] [Decent g],
      Decent (f ≫ g))

/- Lemma 68.17.6 (3): Being reasonable is preserved under compositions. -/
@[stacks 03L1]
#check (AlgebraicGeometry.AlgebraicSpace.reasonable_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@Reasonable S : MorphismProperty (AlgebraicSpace S)))

#check (AlgebraicGeometry.AlgebraicSpace.reasonable_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y ⟶ Z) [Reasonable f] [Reasonable g],
      Reasonable (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
