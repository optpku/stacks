/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AffineCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

universe u v

/- Lemma 87.18.3: A formal algebraic space is affine formal if and only if its
canonical reduction is affine. -/
@[stacks 0DE8] #check
  (AlgebraicGeometry.IsFormalAlgebraicSpace.isAffineFormalAlgebraicSpace_iff_isAffine_reduction :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsFormalAlgebraicSpace X],
      IsAffineFormalAlgebraicSpace X ↔
        ChosenBigFppfSite.IsAffine (IsFormalAlgebraicSpace.reduction X))
