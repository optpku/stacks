module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions

/-!
# Ascent of types along representable morphisms of affine formal algebraic spaces

Countable indexing, classicality, weak adicity, adic*, and Noetherianity
ascend under the corresponding hypotheses on a representable morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A representable morphism of affine formal algebraic spaces with countably indexed
target has countably indexed source. -/
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

/-- A representable morphism of affine formal algebraic spaces with countably indexed
classical target has classical source. -/
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

/-- A representable morphism of affine formal algebraic spaces with weakly adic
target has weakly adic source. -/
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

/-- A representable morphism of affine formal algebraic spaces with adic*
target has adic* source. -/
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

/-- A representable morphism of affine formal algebraic spaces that is locally of
finite type and has Noetherian target has Noetherian source. -/
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
