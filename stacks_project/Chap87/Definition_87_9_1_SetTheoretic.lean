/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Size

/-!
# Definition 87.9.1 set-theoretic compatibility bridge

The fixed-site presentation condition is owned by
`ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Size`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/- Definition 87.9.1 set-theoretic presentation condition -/
#check (IsCoequalizerOfRepresentables :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

end AlgebraicGeometry.ChosenBigFppfSite
