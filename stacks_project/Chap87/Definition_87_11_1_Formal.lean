module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

#check (AlgebraicGeometry.IsFormalAlgebraicSpace :
  ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
