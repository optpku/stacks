/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Adic
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

universe u v

/- Definition 87.23.2: Let `S` be a scheme and let `f : X ⟶ Y` be a morphism
of locally adic* formal algebraic spaces over `S`. The morphism is adic exactly
when it is representable by algebraic spaces. -/
@[stacks 0AQ3] #check
  (AlgebraicGeometry.Adic :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
      [IsLocallyAdicStar X] [IsLocallyAdicStar Y] (f : X ⟶ Y), Prop)
