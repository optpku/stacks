/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.Representability
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Proposition 44.2.6: if every `d`-tuple of points in a fiber of `X ⟶ S` is
contained in an affine open of `X`, then the degree-`d` Hilbert functor is representable
by a scheme. -/
@[stacks 0B9A] #check
  (AlgebraicGeometry.Hilbert.functor_isRepresentable_of_fiber_points_contained_in_affineOpen :
    ∀ {S : Scheme.{u}} (X : Over S) (d : ℕ)
      [AlgebraicGeometry.Hilbert.FiberPointsContainedInAffineOpen X d],
      (AlgebraicGeometry.Hilbert.functor X d).IsRepresentable)
