/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
import StacksCheckRecall

/-!
# Morphisms of algebraic spaces are representable by algebraic spaces

A morphism of algebraic spaces over a scheme `S` is representable by algebraic
spaces in the sense of `representableByAlgebraicSpaces`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.3.2 -/
@[stacks 03BN] #check (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.of_hom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    representableByAlgebraicSpaces f)

#check (AlgebraicGeometry.AlgebraicSpace.instIsAlgebraicSpace_pullback_hom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {U : Over S} (ξ : yoneda.obj U ⟶ Y.functorOfPoints),
      IsAlgebraicSpace (pullback ξ f))

end AlgebraicGeometry.AlgebraicSpace
