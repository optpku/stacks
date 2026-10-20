/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion.Rational
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter

universe u

open AlgebraicGeometry CategoryTheory

/- The rational-completion compatibility module exposes the dependent product
of rationalized nonnegative Chow-cohomology degrees. -/
#check (ChowCohomology.Nonnegative.RationalCompletion :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p],
    Type (u + 1))
