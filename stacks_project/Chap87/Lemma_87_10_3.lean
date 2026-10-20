module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions
import StacksCheckRecall

/-!
# Lemma 87.10.3

Implications among types of affine formal algebraic spaces: Noetherian implies
adic*, adic* implies adic, adic implies weakly adic, weakly adic implies
classical, weakly adic implies countably indexed, and countably indexed
implies McQuillan.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/- Lemma 87.10.3 (1): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is Noetherian, then `X` is adic*. -/
@[stacks 0AIK] #check (AlgebraicGeometry.IsAdicStar.of_isNoetherianAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsNoetherianAffine X], IsAdicStar X)

/- Lemma 87.10.3 (2): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is adic*, then `X` is adic. -/
@[stacks 0AIK] #check (AlgebraicGeometry.IsAdicAffine.of_isAdicStar :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAdicStar X], IsAdicAffine X)

/- Lemma 87.10.3 (3): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is adic, then `X` is weakly adic. -/
@[stacks 0AIK] #check (AlgebraicGeometry.IsWeaklyAdicAffine.of_isAdicAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAdicAffine X], IsWeaklyAdicAffine X)

/- Lemma 87.10.3 (4): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is weakly adic, then `X` is classical. -/
@[stacks 0AIK] #check (AlgebraicGeometry.IsClassicalAffine.of_isWeaklyAdicAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsWeaklyAdicAffine X], IsClassicalAffine X)

/- Lemma 87.10.3 (5): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is weakly adic, then `X` is countably indexed. -/
@[stacks 0AIK] #check (AlgebraicGeometry.IsCountablyIndexedAffine.of_isWeaklyAdicAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsWeaklyAdicAffine X], IsCountablyIndexedAffine X)

/- Lemma 87.10.3 (6): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is countably indexed, then `X` is McQuillan. -/
@[stacks 0AIK] #check (AlgebraicGeometry.IsMcQuillan.of_isCountablyIndexedAffine :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCountablyIndexedAffine X], IsMcQuillan X)

end AlgebraicGeometry
