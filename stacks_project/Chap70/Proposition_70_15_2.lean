module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.AffineDescent
import StacksCheckRecall

/-!
# Proposition 70.15.2

A surjective universally closed morphism of algebraic spaces from an affine
source forces the target to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Proposition 70.15.2: if `f : X ⟶ Y` is a surjective universally closed
morphism of algebraic spaces over a scheme `S` and `X` is affine, then `Y` is
affine. -/
@[stacks 07VT] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAffine.of_surjective_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      Surjective f → UniversallyClosed f → IsAffine X → IsAffine Y)
