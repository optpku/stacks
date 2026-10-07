module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Affine étale covers of algebraic spaces

A special covering of an algebraic space is a surjective étale morphism from a small
coproduct of affine schemes over the base, each of which maps into an affine open of the
base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The object of `Over S` whose underlying scheme is the coproduct of a small family of
schemes over `S`. -/
def sigmaMk {I : Type v} [Small.{u} I] (U : I → Over S) : Over S :=
  Over.mk (Sigma.desc fun i ↦ (U i).hom)

/-- The underlying scheme of `sigmaMk U` is the coproduct of the underlying schemes. -/
theorem sigmaMk_left {I : Type v} [Small.{u} I] (U : I → Over S) :
    (sigmaMk U).left = ∐ fun i ↦ (U i).left :=
  sorry

/-- The structure morphism of `sigmaMk U` is the coproduct descent of the structure morphisms. -/
theorem sigmaMk_hom {I : Type v} [Small.{u} I] (U : I → Over S) :
    (sigmaMk U).hom = Sigma.desc fun i ↦ (U i).hom :=
  sorry

/-- The coproduct inclusion of a summand commutes with the structure morphisms to `S`. -/
theorem sigmaι_w {I : Type v} [Small.{u} I] (U : I → Over S) (i : I) :
    Sigma.ι (fun j ↦ (U j).left) i ≫ (sigmaMk U).hom = (U i).hom :=
  sorry

/-- The inclusion of the `i`-th summand into the scheme coproduct, as a morphism over `S`. -/
def sigmaι {I : Type v} [Small.{u} I] (U : I → Over S) (i : I) : U i ⟶ sigmaMk U :=
  Over.homMk (Sigma.ι (fun j ↦ (U j).left) i) (sigmaι_w U i)

/-- The underlying scheme morphism of `sigmaι U i` is the coproduct inclusion. -/
theorem sigmaι_left {I : Type v} [Small.{u} I] (U : I → Over S) (i : I) :
    (sigmaι U i).left = Sigma.ι (fun j ↦ (U j).left) i :=
  sorry

/-- An étale-surjective atlas of an algebraic space by a small coproduct of affine schemes
over `S`, each of which maps into an affine open of `S`. -/
structure AffineEtaleCover (X : AlgebraicSpace S) where
  /-- The index type of the affine summands. -/
  I : Type v
  /-- The index type is `u`-small, so the scheme coproduct exists. -/
  [small : Small.{u} I]
  /-- The family of affine schemes over `S`. -/
  component : I → Over S
  /-- Each summand is an affine scheme. -/
  isAffine : ∀ i, IsAffine (component i).left
  /-- An affine open of `S` containing the image of each summand. -/
  targetOpen : I → S.Opens
  /-- Each target open of `S` is affine. -/
  isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i)
  /-- Each summand maps into the chosen affine open of `S`. -/
  range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i
  /-- The atlas morphism from the coproduct of the summands. -/
  hom : ofOver (sigmaMk component) ⟶ X
  /-- The atlas is representable and étale. -/
  etale : (MorphismProperty.over (@Etale)).presheaf hom
  /-- The atlas is étale-locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom

namespace AffineEtaleCover

variable {X : AlgebraicSpace S}

/-- Pack a small affine family over `S`, affine opens of `S` containing the images, and an
étale locally surjective map out of the scheme coproduct into an `AffineEtaleCover`. -/
def ofFamily {I : Type v} [Small.{u} I] (component : I → Over S)
    (isAffine : ∀ i, IsAffine (component i).left) (targetOpen : I → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i)
    (hom : ofOver (sigmaMk component) ⟶ X)
    (etale : (MorphismProperty.over (@Etale)).presheaf hom)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom) :
    AffineEtaleCover X where
  I := I
  component := component
  isAffine := isAffine
  targetOpen := targetOpen
  isAffineOpen_targetOpen := isAffineOpen_targetOpen
  range_subset_targetOpen := range_subset_targetOpen
  hom := hom
  etale := etale
  locallySurjective := locallySurjective

/-- The index type of `ofFamily` is the given index type. -/
@[simp]
theorem ofFamily_I {I : Type v} [Small.{u} I] (component : I → Over S)
    (isAffine : ∀ i, IsAffine (component i).left) (targetOpen : I → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i)
    (hom : ofOver (sigmaMk component) ⟶ X)
    (etale : (MorphismProperty.over (@Etale)).presheaf hom)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom) :
    (ofFamily component isAffine targetOpen isAffineOpen_targetOpen range_subset_targetOpen hom
        etale locallySurjective).I =
      I :=
  sorry

/-- The component family of `ofFamily` is the given family of schemes over `S`. -/
@[simp]
theorem ofFamily_component {I : Type v} [Small.{u} I] (component : I → Over S)
    (isAffine : ∀ i, IsAffine (component i).left) (targetOpen : I → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i)
    (hom : ofOver (sigmaMk component) ⟶ X)
    (etale : (MorphismProperty.over (@Etale)).presheaf hom)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom) :
    (ofFamily component isAffine targetOpen isAffineOpen_targetOpen range_subset_targetOpen hom
        etale locallySurjective).component =
      component :=
  sorry

/-- The atlas morphism of `ofFamily` is the given morphism from the scheme coproduct. -/
@[simp]
theorem ofFamily_hom {I : Type v} [Small.{u} I] (component : I → Over S)
    (isAffine : ∀ i, IsAffine (component i).left) (targetOpen : I → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i)
    (hom : ofOver (sigmaMk component) ⟶ X)
    (etale : (MorphismProperty.over (@Etale)).presheaf hom)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom) :
    (ofFamily component isAffine targetOpen isAffineOpen_targetOpen range_subset_targetOpen hom
        etale locallySurjective).hom =
      hom :=
  sorry

/-- An affine étale cover is a coproduct of affine schemes over `S`, each mapping into an
affine open of `S`, with étale locally surjective atlas morphism. -/
theorem spec (𝒰 : AffineEtaleCover X) :
    (∀ i, IsAffine (𝒰.component i).left) ∧
      (∀ i, IsAffineOpen (𝒰.targetOpen i)) ∧
        (∀ i, Set.range (𝒰.component i).hom ⊆ 𝒰.targetOpen i) ∧
          (MorphismProperty.over (@Etale)).presheaf 𝒰.hom ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) 𝒰.hom :=
  sorry

/-- The composite atlas map of the `i`-th affine summand. -/
def componentHom (𝒰 : AffineEtaleCover X) (i : 𝒰.I) : ofOver (𝒰.component i) ⟶ X :=
  ofOverMap (sigmaι 𝒰.component i) ≫ 𝒰.hom

/-- `componentHom 𝒰 i` is the composite of the coproduct inclusion with the atlas. -/
theorem componentHom_eq (𝒰 : AffineEtaleCover X) (i : 𝒰.I) :
    𝒰.componentHom i = ofOverMap (sigmaι 𝒰.component i) ≫ 𝒰.hom :=
  sorry

end AffineEtaleCover

/-- Every algebraic space over a scheme `S` admits a surjective étale atlas from a coproduct of
affine schemes over `S`, each of which maps into an affine open of `S`. -/
theorem exists_affineEtaleCover (X : AlgebraicSpace S) :
    Nonempty (AffineEtaleCover.{u} X) :=
  sorry

/-- A surjective étale atlas from a scheme yields an affine étale cover, by Zariski-refining so
that each piece maps into an affine open of `S` and passing to the disjoint union. -/
theorem exists_of_etaleAtlas {X : AlgebraicSpace S} {V : Over S} (f : ofOver V ⟶ X)
    (hetale : (MorphismProperty.over (@Etale)).presheaf f)
    (hsurj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f) :
    Nonempty (AffineEtaleCover.{u} X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
