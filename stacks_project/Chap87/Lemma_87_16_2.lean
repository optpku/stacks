/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.ReductionSeparation
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

universe u v

/- Lemma 87.16.2: The reduction of a formal algebraic space is absolutely
separated if and only if all affine tests have affine fibre products with
surjective canonical `ℤ`-tensor maps on global sections. -/
@[stacks 0AJ6] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.tfae_separated :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier},
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] →
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] →
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] →
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) →
    [IsFormalAlgebraicSpace X] →
    List.TFAE [ChosenBigFppfSite.IsSeparated (reduction X),
      forallAffinePullbackAffineSurjective X])
