/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.QuasiCompact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v

/- Lemma 87.17.1: A formal algebraic space has quasi-compact reduction if and
only if it admits a finite affine étale atlas, equivalently a single
representable étale surjection from an affine formal algebraic space. -/
@[stacks 0AJ9] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.tfae_quasiCompact :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsFormalAlgebraicSpace X],
    List.TFAE [ChosenBigFppfSite.IsQuasiCompact (IsFormalAlgebraicSpace.reduction X),
      IsFormalAlgebraicSpace.HasFiniteAffineEtaleAtlas X,
      IsFormalAlgebraicSpace.HasAffineEtaleCover X])
