module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

universe u v

/- Definition 87.10.2: for a scheme `S` and an affine formal algebraic space
`X` over `S`, we say `X` is countably indexed if the equivalent conditions of
Lemma 87.10.1 hold. -/
@[stacks 0AIJ] #check (AlgebraicGeometry.IsCountablyIndexedAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
