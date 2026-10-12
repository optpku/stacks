/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.38.11: if `X ⟶ Z` is unramified then `X ⟶ Y` is unramified. -/
@[stacks 06G6] #check
  (AlgebraicGeometry.AlgebraicSpace.Unramified.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [Unramified (f ≫ g)], Unramified f)
