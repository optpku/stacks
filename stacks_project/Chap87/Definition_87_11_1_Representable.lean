module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

#check (AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces :
  ∀ {𝒮 : AlgebraicGeometry.ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}, (X ⟶ Y) → Prop)
