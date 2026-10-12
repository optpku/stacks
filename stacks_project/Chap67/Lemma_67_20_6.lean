/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.20.6: A closed immersion of algebraic spaces is affine. -/
@[stacks 07U2]
#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.affine :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsClosedImmersion f] → Affine f)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.le_affine :
  ∀ {S : Scheme.{u}},
    (@IsClosedImmersion S : MorphismProperty (AlgebraicSpace S)) ≤
      (@Affine S : MorphismProperty (AlgebraicSpace S)))

end AlgebraicGeometry.AlgebraicSpace
