module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

universe u v

/- Lemma 87.10.3: the affine type conditions used in the implications between
Noetherian, adic*, adic, weakly adic, classical, countably indexed, and
McQuillan affine formal algebraic spaces. -/
@[stacks 0AIK] #check (AlgebraicGeometry.IsNoetherianAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
