/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.19.2: A composition of formally smooth morphisms of algebraic
spaces is formally smooth. -/
@[stacks 061E] #check (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.comp :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallySmooth f] [FormallySmooth g], FormallySmooth (f ≫ g))

end AlgebraicGeometry.AlgebraicSpace
