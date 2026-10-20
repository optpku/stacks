/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalRepresentability
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u v

/- Lemma 87.19.4. Representability by algebraic spaces for morphisms of formal
algebraic spaces is equivalent to the square and affine étale covering criteria. -/
@[stacks 0AN4] #check
  (AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces.tfae :
    ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [CategoryTheory.Limits.HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)
      [AlgebraicGeometry.IsFormalAlgebraicSpace X]
      [AlgebraicGeometry.IsFormalAlgebraicSpace Y],
      List.TFAE
        [AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces f,
          AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces.existsSurjectiveEtaleSquare f,
          AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces.forallVerticalRepresentable f,
          AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces.existsCoverOnTarget f,
          AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces.existsCoverOnSource f])
