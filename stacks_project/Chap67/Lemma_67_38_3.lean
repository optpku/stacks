/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.38.3: The composition of unramified morphisms is unramified. -/
@[stacks 03ZI] #check
  (AlgebraicGeometry.AlgebraicSpace.unramified_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.Unramified S :
        MorphismProperty (AlgebraicSpace S)))

#check
  (AlgebraicGeometry.AlgebraicSpace.unramified_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.AlgebraicSpace.Unramified f]
      [AlgebraicGeometry.AlgebraicSpace.Unramified g],
      AlgebraicGeometry.AlgebraicSpace.Unramified (f ≫ g))
