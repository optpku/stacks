/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing

/-!
# Strict henselization of an algebraic space at a geometric point

The strict henselization of an algebraic space at a geometric point is the spectrum of
the étale local ring at that geometric point.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The strict henselization of an algebraic space at a geometric point is the spectrum of
the étale local ring at that geometric point. -/
noncomputable def strictHenselizationScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) : Scheme.{u} :=
  Spec (CommRingCat.of (etaleLocalRing X xbar))

/-- The strict henselization scheme is definitionally the spectrum of the étale local
ring. -/
theorem strictHenselizationScheme_def {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    strictHenselizationScheme xbar = Spec (CommRingCat.of (etaleLocalRing X xbar)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
