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

/- Lemma 87.16.1: The reduction of a formal algebraic space is a quasi-separated
algebraic space if and only if fibre products of arbitrary morphisms from
quasi-compact schemes are quasi-compact, equivalently if the same holds for
affine schemes. -/
@[stacks 0AJ5] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.tfae_quasiSeparated :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier},
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)] →
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] →
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] →
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) →
    [IsFormalAlgebraicSpace X] →
    List.TFAE [ChosenBigFppfSite.IsQuasiSeparated (reduction X),
      forallQuasiCompactPullback X, forallAffineQuasiCompactPullback X])
