/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalTypes
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/- Lemma 87.20.10 -/
#check (IsLocallyCountablyIndexed : ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
  [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
  [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
  (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
#check (IsLocallyClassical : ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
  [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
  [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
  (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
#check (IsLocallyWeaklyAdic : ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
  [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
  [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
  (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
#check (IsFormalAlgebraicSpace.IsLocallyNoetherian : ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
  [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
  [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
  (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
#check (IsFormalAlgebraicSpace.reduction : ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
  [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
  [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
  (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsFormalAlgebraicSpace X],
  Sheaf (𝒮.bigTopology S) (Type (max u v)))
#check (IsFormalAlgebraicSpace.reductionι : ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
  [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
  [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
  (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsFormalAlgebraicSpace X],
  IsFormalAlgebraicSpace.reduction X ⟶ X)

end AlgebraicGeometry
end
