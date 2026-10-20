module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicTypes
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions

/-!
# Flat descent of types of affine formal algebraic spaces

A surjective flat morphism between affine formal algebraic spaces that is
representable by algebraic spaces preserves the adic* property, weak adicity,
and the conjunction of countable indexing and classicality in both directions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- For a surjective flat morphism of affine formal algebraic spaces that is
representable by algebraic spaces, the source is adic* if and only if the target
is adic*. -/
@[stacks 0AKT]
theorem IsAdicStar.iff_of_surjective_flat
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f)
    (h_surjective : (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_flat : (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f) :
    IsAdicStar X ↔ IsAdicStar Y :=
  sorry

/-- For a surjective flat morphism of affine formal algebraic spaces that is
representable by algebraic spaces, the source is countably indexed and classical
if and only if the target is countably indexed and classical. -/
@[stacks 0GXR]
theorem IsClassicalAffine.iff_of_surjective_flat
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f)
    (h_surjective : (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_flat : (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f) :
    IsCountablyIndexedAffine X ∧ IsClassicalAffine X ↔
      IsCountablyIndexedAffine Y ∧ IsClassicalAffine Y :=
  sorry

/-- For a surjective flat morphism of affine formal algebraic spaces that is
representable by algebraic spaces, the source is weakly adic if and only if the
target is weakly adic. -/
@[stacks 0GXS]
theorem IsWeaklyAdicAffine.iff_of_surjective_flat
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f)
    (h_surjective : (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f)
    (h_flat : (MorphismProperty.inverseImage (@Flat : MorphismProperty Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f) :
    IsWeaklyAdicAffine X ↔ IsWeaklyAdicAffine Y :=
  sorry

end AlgebraicGeometry
