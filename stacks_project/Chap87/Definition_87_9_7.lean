module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicTypes
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry

universe u v

/- Definition 87.9.7 (1): for a scheme `S` and an affine formal algebraic space
`X` over `S`, we say `X` is McQuillan if `X` satisfies the equivalent
conditions of Lemma 87.9.6. -/
@[stacks 0AID] #check (AlgebraicGeometry.IsMcQuillan :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.9.7 (2): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is classical if `X` is McQuillan and `A` is
admissible. -/
@[stacks 0AID] #check (AlgebraicGeometry.IsClassicalAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.9.7 (3): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is weakly adic if `X` is McQuillan and `A` is
weakly adic. -/
@[stacks 0AID] #check (AlgebraicGeometry.IsWeaklyAdicAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.9.7 (4): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is adic if `X` is McQuillan and `A` is adic. -/
@[stacks 0AID] #check (AlgebraicGeometry.IsAdicAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.9.7 (5): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is adic* if `X` is McQuillan, `A` is adic, and
`A` has a finitely generated ideal of definition. -/
@[stacks 0AID] #check (AlgebraicGeometry.IsAdicStar :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

/- Definition 87.9.7 (6): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is Noetherian if `X` is McQuillan and `A` is
both Noetherian and adic. -/
@[stacks 0AID] #check (AlgebraicGeometry.IsNoetherianAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
