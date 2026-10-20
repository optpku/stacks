/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Endomorphism

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- The historical import path reexports the reusable Chern-polynomial API. -/
#check
  (AlgebraicGeometry.ChernPolynomial.homogeneousValue :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p) (E : X.Modules)
      [E.IsFiniteLocallyFree] (P : MvPolynomial ℕ ℤ) (n : ℕ),
      MvPolynomial.IsWeightedHomogeneous id P n →
        AlgebraicGeometry.ChowCohomology.Nonnegative.degree δ p n)
