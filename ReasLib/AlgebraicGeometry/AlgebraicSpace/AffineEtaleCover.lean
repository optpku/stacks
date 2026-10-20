module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.Coproduct.Over

/-!
# Affine étale covers of algebraic spaces

An affine étale cover is an étale locally surjective atlas from a small coproduct of affine
schemes, each mapping into a specified affine open of the base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- An étale-surjective atlas of an algebraic space by a small coproduct of affine schemes
over `S`, each of which maps into an affine open of `S`. -/
structure AffineEtaleCover (X : AlgebraicSpace S) where
  /-- The index type of the affine summands. -/
  I : Type v
  /-- The index type is `u`-small, so the scheme coproduct exists. -/
  small : Small.{u} I
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
  hom : ofOver (Scheme.Coproduct.overMk (small := small) component) ⟶ X
  /-- The atlas is representable and étale. -/
  etale : (MorphismProperty.over (@Etale)).presheaf hom
  /-- The atlas is étale-locally surjective. -/
  locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom

namespace AffineEtaleCover

variable {X : AlgebraicSpace S}

/-- Pack a small affine family over `S`, affine opens of `S` containing the images, and an
étale locally surjective map out of the scheme coproduct into an `AffineEtaleCover`. -/
def ofFamily {I : Type v} [small : Small.{u} I] (component : I → Over S)
    (isAffine : ∀ i, IsAffine (component i).left) (targetOpen : I → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i)
    (hom : ofOver (Scheme.Coproduct.overMk (small := small) component) ⟶ X)
    (etale : (MorphismProperty.over (@Etale)).presheaf hom)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom) :
    AffineEtaleCover X where
  I := I
  small := small
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
theorem ofFamily_I {I : Type v} [small : Small.{u} I] (component : I → Over S)
    (isAffine : ∀ i, IsAffine (component i).left) (targetOpen : I → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i)
    (hom : ofOver (Scheme.Coproduct.overMk (small := small) component) ⟶ X)
    (etale : (MorphismProperty.over (@Etale)).presheaf hom)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom) :
    (ofFamily component isAffine targetOpen isAffineOpen_targetOpen range_subset_targetOpen hom
        etale locallySurjective).I =
      I :=
  rfl

/-- The component family of `ofFamily` is the given family of schemes over `S`. -/
@[simp]
theorem ofFamily_component {I : Type v} [small : Small.{u} I] (component : I → Over S)
    (isAffine : ∀ i, IsAffine (component i).left) (targetOpen : I → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i)
    (hom : ofOver (Scheme.Coproduct.overMk (small := small) component) ⟶ X)
    (etale : (MorphismProperty.over (@Etale)).presheaf hom)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom) :
    (ofFamily component isAffine targetOpen isAffineOpen_targetOpen range_subset_targetOpen hom
        etale locallySurjective).component =
      component :=
  rfl

/-- The atlas morphism of `ofFamily` is the given morphism from the scheme coproduct. -/
@[simp]
theorem ofFamily_hom {I : Type v} [small : Small.{u} I] (component : I → Over S)
    (isAffine : ∀ i, IsAffine (component i).left) (targetOpen : I → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (component i).hom ⊆ targetOpen i)
    (hom : ofOver (Scheme.Coproduct.overMk (small := small) component) ⟶ X)
    (etale : (MorphismProperty.over (@Etale)).presheaf hom)
    (locallySurjective : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) hom) :
    (ofFamily component isAffine targetOpen isAffineOpen_targetOpen range_subset_targetOpen hom
        etale locallySurjective).hom =
      hom :=
  rfl

/-- An affine étale cover is a coproduct of affine schemes over `S`, each mapping into an
affine open of `S`, with étale locally surjective atlas morphism. -/
theorem spec (𝒰 : AffineEtaleCover X) :
    (∀ i, IsAffine (𝒰.component i).left) ∧
      (∀ i, IsAffineOpen (𝒰.targetOpen i)) ∧
        (∀ i, Set.range (𝒰.component i).hom ⊆ 𝒰.targetOpen i) ∧
          (MorphismProperty.over (@Etale)).presheaf 𝒰.hom ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) 𝒰.hom :=
  ⟨𝒰.isAffine, 𝒰.isAffineOpen_targetOpen, 𝒰.range_subset_targetOpen,
    𝒰.etale, 𝒰.locallySurjective⟩

/-- The composite atlas map of the `i`-th affine summand. -/
def componentHom (𝒰 : AffineEtaleCover X) (i : 𝒰.I) : ofOver (𝒰.component i) ⟶ X :=
  yoneda.map (Scheme.Coproduct.overι (small := 𝒰.small) 𝒰.component i) ≫ 𝒰.hom

/-- `componentHom 𝒰 i` is the composite of the coproduct inclusion with the atlas. -/
theorem componentHom_eq (𝒰 : AffineEtaleCover X) (i : 𝒰.I) :
    𝒰.componentHom i = yoneda.map (Scheme.Coproduct.overι (small := 𝒰.small) 𝒰.component i) ≫ 𝒰.hom :=
  rfl

end AffineEtaleCover

/-- A surjective étale atlas from a scheme yields an affine étale cover, by Zariski-refining so
that each piece maps into an affine open of `S` and passing to the disjoint union. -/
theorem exists_of_etaleAtlas {X : AlgebraicSpace S} {V : Over S} (f : ofOver V ⟶ X)
    (hetale : (MorphismProperty.over (@Etale)).presheaf f)
    (hsurj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f) :
    Nonempty (AffineEtaleCover.{u, u} X) :=
  sorry

/-- Every algebraic space over a scheme `S` admits a surjective étale atlas from a coproduct of
affine schemes over `S`, each of which maps into an affine open of `S`. -/
theorem exists_affineEtaleCover (X : AlgebraicSpace S) :
    Nonempty (AffineEtaleCover.{u, u} X) := by
  obtain ⟨V, f, hetale, hsurj⟩ := X.atlas
  exact exists_of_etaleAtlas f hetale hsurj

end AlgebraicGeometry.AlgebraicSpace
