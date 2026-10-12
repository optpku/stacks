/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_6_4_Pushforward
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.6.4: derived pushforward along an affine morphism of algebraic spaces
reflects isomorphisms. -/
@[stacks 08II] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.reflectsIsomorphisms_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f],
      (pushforward f).ReflectsIsomorphisms)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
