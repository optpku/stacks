/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction
@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite
universe u v
#check (AlgebraicGeometry.IsFormalAlgebraicSpace.reduction : ∀ {𝒮 : ChosenBigFppfSite.{u,v}} {S : 𝒮.carrier}
 [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
 [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
 (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [AlgebraicGeometry.IsFormalAlgebraicSpace X],
 Sheaf (𝒮.bigTopology S) (Type (max u v)))
#check (AlgebraicGeometry.IsFormalAlgebraicSpace.reductionι : ∀ {𝒮 : ChosenBigFppfSite.{u,v}} {S : 𝒮.carrier}
 [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
 [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
 (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [AlgebraicGeometry.IsFormalAlgebraicSpace X],
 AlgebraicGeometry.IsFormalAlgebraicSpace.reduction X ⟶ X)
