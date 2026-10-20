/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FilteredK0.Image

@[expose] public section

open CategoryTheory

universe u

/- Lemma 42.69.3: The canonical map from `CH_k(X)` to
`K₀(Coh≤k+1(X) / Coh≤k-1(X))` is a bijection onto the image of the
transition from `K₀(Coh≤k(X) / Coh≤k-1(X))`. -/
@[stacks 02SC] #check
  (AlgebraicGeometry.ChowGroup.toFilteredK0_bijOn :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ),
      Set.BijOn (AlgebraicGeometry.ChowGroup.toFilteredK0 p δ k) Set.univ
        (AlgebraicGeometry.Scheme.Modules.GradedK0.filteredImage p δ k))
