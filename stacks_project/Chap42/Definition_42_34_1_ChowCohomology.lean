/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.ChowCohomology.ring :
  ∀ {S X : Scheme.{u}} (delta : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction delta] [LocallyOfFiniteType p],
    Type (u + 1))
