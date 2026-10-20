/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction

/-! # Lemma 87.12.1 -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace
noncomputable section
universe u v
/- Lemma 87.12.1 -/
@[stacks 0AIN] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.reduction_properties :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X],
    ChosenBigFppfSite.IsReduced (reduction X) ∧ representableByAlgebraicSpaces (reductionι X) ∧
      (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (reductionι X) ∧
      ∀ (U : Sheaf (𝒮.bigTopology S) (Type (max u v))) [ChosenBigFppfSite.IsReduced U]
        (g : U ⟶ X), ∃! h : U ⟶ reduction X, h ≫ reductionι X = g)
