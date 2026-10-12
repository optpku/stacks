/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Pullback

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- This historical module publicly re-exports the triangle pullback API. -/
#check
  (AlgebraicGeometry.Scheme.DeRham.Cohomology.baseRingSquare_comm :
    ∀ {X S : Scheme.{u}} (p : X ⟶ S) [IsAffine S],
      𝟙 X ≫ (p ≫ S.isoSpec.hom) = p ≫ S.isoSpec.hom)
