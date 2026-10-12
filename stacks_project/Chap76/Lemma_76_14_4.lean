/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified
import StacksCheckRecall

/-!
# Composition of formally unramified morphisms of algebraic spaces

A composition of formally unramified morphisms of algebraic spaces is formally
unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.14.4: A composition of formally unramified morphisms of algebraic
spaces is formally unramified. -/
@[stacks 05ZZ] #check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [FormallyUnramified f] [FormallyUnramified g], FormallyUnramified (f ≫ g))

#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.instIsStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@FormallyUnramified S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
