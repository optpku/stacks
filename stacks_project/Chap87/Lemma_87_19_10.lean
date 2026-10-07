module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_9_1_Affine
public import stacks_project.Chap87.Lemma_87_10_3_Types

/-!
# Lemma 87.19.10

Countably indexed, classical, weakly adic, adic*, and Noetherian types ascend
along a morphism of affine formal algebraic spaces that is representable by
algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- Lemma 87.19.10 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces. If
`Y` is countably indexed, then `X` is countably indexed. -/
@[stacks 0AKQ]
theorem IsCountablyIndexedAffine.of_representableByAlgebraicSpaces
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsCountablyIndexedAffine Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f) :
    IsCountablyIndexedAffine X :=
  sorry

/-- Lemma 87.19.10 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces. If
`Y` is countably indexed and classical, then `X` is countably indexed and
classical. -/
@[stacks 0AKQ]
theorem IsClassicalAffine.of_representableByAlgebraicSpaces
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsCountablyIndexedAffine Y]
    [IsClassicalAffine Y] {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f) :
    IsClassicalAffine X :=
  sorry

/-- Lemma 87.19.10 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces. If
`Y` is weakly adic, then `X` is weakly adic. -/
@[stacks 0AKQ]
theorem IsWeaklyAdicAffine.of_representableByAlgebraicSpaces
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsWeaklyAdicAffine Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f) :
    IsWeaklyAdicAffine X :=
  sorry

/-- Lemma 87.19.10 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces. If
`Y` is adic*, then `X` is adic*. -/
@[stacks 0AKQ]
theorem IsAdicStar.of_representableByAlgebraicSpaces
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAdicStar Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f) :
    IsAdicStar X :=
  sorry

/-- Lemma 87.19.10 (5): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces. If
`Y` is Noetherian and `f` is locally of finite type, then `X` is Noetherian. -/
@[stacks 0AKQ]
theorem IsNoetherianAffine.of_representableByAlgebraicSpaces
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsNoetherianAffine Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f)
    (hft : (MorphismProperty.inverseImage (@LocallyOfFiniteType)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f) :
    IsNoetherianAffine X :=
  sorry

end AlgebraicGeometry
