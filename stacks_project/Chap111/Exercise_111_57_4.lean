/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AffinePlane.ExceptionalDivisor

/-!
# Exercise 111.57.4

The scheme-theoretic fibre of the blowup of the affine plane in the origin is
isomorphic to `P¹_k`, is an effective Cartier divisor, and has conormal line
bundle of degree one.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.AffinePlaneBlowup

/- Exercise 111.57.4 (1) -/
@[stacks 0AAQ] #check (AlgebraicGeometry.AffinePlaneBlowup.exceptionalFiber_isIsomorphic_projectiveLine :
  ∀ (k : Type u) [Field k],
    IsIsomorphic (Over.mk (AlgebraicGeometry.AffinePlaneBlowup.exceptionalToSpec k))
      (ProjectiveSpace.schemeOver k 1))

/- Exercise 111.57.4 (2) -/
@[stacks 0AAQ] #check (AlgebraicGeometry.AffinePlaneBlowup.exceptionalι_isEffectiveCartierDivisor :
  ∀ (k : Type u) [Field k],
    IsEffectiveCartierDivisor (AlgebraicGeometry.AffinePlaneBlowup.exceptionalι k))

/- Exercise 111.57.4 (3) -/
@[stacks 0AAQ] #check (AlgebraicGeometry.AffinePlaneBlowup.restriction_curveDegree_eq_one :
  ∀ (k : Type u) [Field k],
    Scheme.Modules.curveDegreeOfInvertible (exceptionalToSpec k)
      (exceptionalFiber_topologicalKrullDim_le_one k) (restriction k) = 1)

end AlgebraicGeometry.AffinePlaneBlowup
