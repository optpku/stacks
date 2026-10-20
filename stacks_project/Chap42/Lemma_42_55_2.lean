/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Compactification

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry MonoidalCategory

universe u

/- Lemma 42.55.2 (1): the derived Chern components of the pushed-forward structure module
along the zero section vanish in all positive degrees strictly below the vector-bundle rank. -/
@[stacks 0FEF] #check
  (AlgebraicGeometry.ChowCohomology.ChernClass.Compactification.component_eq_zero :
    ∀ {S X E : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] (C : X.Modules) (r : ℕ)
      [C.IsFiniteLocallyFreeOfRank r] (π : E ⟶ X)
      (hπ : Scheme.ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))
      (t : ℕ), 0 < t → t < r →
      AlgebraicGeometry.ChowCohomology.ChernClass.Compactification.component
        δ p C r π hπ t = 0)

/- Lemma 42.55.2 (2): the degree-r derived Chern operation followed by projective
pushforward and vector-bundle pullback is the signed factorial multiple of the canonical
inclusion pullback as a degree-zero operational class on the projection cospan. -/
@[stacks 0FEF] #check
  (AlgebraicGeometry.ChowCohomology.ChernClass.Compactification.pushPull_component :
    ∀ {S X E : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] (C : X.Modules) (r : ℕ)
      [C.IsFiniteLocallyFreeOfRank r] (π : E ⟶ X)
      (hπ : Scheme.ProjectiveBundle.Representation π (C ⊞ 𝟙_ X.Modules))
      (V : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra C))
      [Scheme.IsRelativeSpectrumOver V], 0 < r →
      AlgebraicGeometry.ChowCohomology.ChernClass.Compactification.pushPullComponent
        δ p C r π hπ V =
        BivariantClass.Cospan.scale δ
          (((-1 : ℤ) ^ (r - 1)) * (Nat.factorial (r - 1) : ℤ))
          (AlgebraicGeometry.ChowCohomology.ChernClass.Compactification.chartPullback
            δ p C r π hπ V))
