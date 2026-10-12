/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Integral

@[expose] public section

open CategoryTheory

universe u

/- The completed integral nonnegative Chow-cohomology carrier is available from
its reusable mathematical owner. -/
#check
  (AlgebraicGeometry.ChowCohomology.Nonnegative.Completion :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p], Type (u + 1))
