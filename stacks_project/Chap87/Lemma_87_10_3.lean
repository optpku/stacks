/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_10_3_Types

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

/-- Lemma 87.10.3 (1): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is Noetherian, then `X` is adic*. -/
@[stacks 0AIK, instance]
instance IsAdicStar.of_isNoetherianAffine {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsNoetherianAffine X] : IsAdicStar X := sorry

/-- Lemma 87.10.3 (2): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is adic*, then `X` is adic. -/
@[stacks 0AIK, instance]
instance IsAdicAffine.of_isAdicStar {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAdicStar X] : IsAdicAffine X := sorry

/-- Lemma 87.10.3 (3): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is adic, then `X` is weakly adic. -/
@[stacks 0AIK, instance]
instance IsWeaklyAdicAffine.of_isAdicAffine {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAdicAffine X] : IsWeaklyAdicAffine X := sorry

/-- Lemma 87.10.3 (4): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is weakly adic, then `X` is classical. -/
@[stacks 0AIK, instance]
instance IsClassicalAffine.of_isWeaklyAdicAffine {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsWeaklyAdicAffine X] : IsClassicalAffine X := sorry

/-- Lemma 87.10.3 (5): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is weakly adic, then `X` is countably indexed. -/
@[stacks 0AIK, instance]
instance IsCountablyIndexedAffine.of_isWeaklyAdicAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsWeaklyAdicAffine X] : IsCountablyIndexedAffine X := sorry

/-- Lemma 87.10.3 (6): Let `X` be an affine formal algebraic space over a
scheme `S`. If `X` is countably indexed, then `X` is McQuillan. -/
@[stacks 0AIK, instance]
instance IsMcQuillan.of_isCountablyIndexedAffine {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCountablyIndexedAffine X] : IsMcQuillan X := sorry

end AlgebraicGeometry
