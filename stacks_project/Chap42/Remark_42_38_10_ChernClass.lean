/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- A compatibility check for the canonical Chern class assembled from rank loci. -/
#check (AlgebraicGeometry.ChernClass.chernClass :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
    AlgebraicGeometry.ChowCohomology.Nonnegative.degree δ π i)
