/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineEtaleCover

/-!
# Affine étale Zariski covers of algebraic spaces

A special Zariski covering of an algebraic space is a covering by open subspaces each of
which admits a surjective étale atlas from a single affine scheme over the base, mapping
into an affine open of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A Zariski covering of an algebraic space whose members each admit a surjective étale
atlas from a single affine scheme over `S`, mapping into an affine open of `S`. -/
structure AffineEtaleZariskiCover (X : AlgebraicSpace S) where
  /-- The underlying Zariski covering. -/
  cover : ZariskiCover X
  /-- The affine scheme over `S` covering each open subspace. -/
  affine : cover.I₀ → Over S
  /-- Each atlas source is an affine scheme. -/
  isAffine : ∀ i, IsAffine (affine i).left
  /-- The étale atlas of each open subspace from its affine scheme. -/
  atlas : ∀ i, ofOver (affine i) ⟶ cover.X i
  /-- Each atlas is representable and étale. -/
  etale : ∀ i, (MorphismProperty.over (@Etale)).presheaf (atlas i)
  /-- Each atlas is étale-locally surjective. -/
  locallySurjective :
    ∀ i, Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlas i)
  /-- An affine open of `S` containing the image of each affine atlas source. -/
  targetOpen : cover.I₀ → S.Opens
  /-- Each target open of `S` is affine. -/
  isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i)
  /-- Each affine atlas source maps into the chosen affine open of `S`. -/
  range_subset_targetOpen : ∀ i, Set.range (affine i).hom ⊆ targetOpen i

namespace AffineEtaleZariskiCover

variable {X : AlgebraicSpace S}

/-- Pack a Zariski covering together with a single affine étale locally surjective atlas of
each member and affine opens of `S` containing the images. -/
def ofFamily (cover : ZariskiCover X) (affine : cover.I₀ → Over S)
    (isAffine : ∀ i, IsAffine (affine i).left)
    (atlas : ∀ i, ofOver (affine i) ⟶ cover.X i)
    (etale : ∀ i, (MorphismProperty.over (@Etale)).presheaf (atlas i))
    (locallySurjective :
      ∀ i, Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlas i))
    (targetOpen : cover.I₀ → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (affine i).hom ⊆ targetOpen i) :
    AffineEtaleZariskiCover X where
  cover := cover
  affine := affine
  isAffine := isAffine
  atlas := atlas
  etale := etale
  locallySurjective := locallySurjective
  targetOpen := targetOpen
  isAffineOpen_targetOpen := isAffineOpen_targetOpen
  range_subset_targetOpen := range_subset_targetOpen

/-- The underlying Zariski covering of `ofFamily` is the given covering. -/
@[simp]
theorem ofFamily_cover (cover : ZariskiCover X) (affine : cover.I₀ → Over S)
    (isAffine : ∀ i, IsAffine (affine i).left)
    (atlas : ∀ i, ofOver (affine i) ⟶ cover.X i)
    (etale : ∀ i, (MorphismProperty.over (@Etale)).presheaf (atlas i))
    (locallySurjective :
      ∀ i, Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlas i))
    (targetOpen : cover.I₀ → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (affine i).hom ⊆ targetOpen i) :
    (ofFamily cover affine isAffine atlas etale locallySurjective
        targetOpen isAffineOpen_targetOpen range_subset_targetOpen).cover =
      cover :=
  rfl

/-- The affine family of `ofFamily` is the given family of schemes over `S`. -/
@[simp]
theorem ofFamily_affine (cover : ZariskiCover X) (affine : cover.I₀ → Over S)
    (isAffine : ∀ i, IsAffine (affine i).left)
    (atlas : ∀ i, ofOver (affine i) ⟶ cover.X i)
    (etale : ∀ i, (MorphismProperty.over (@Etale)).presheaf (atlas i))
    (locallySurjective :
      ∀ i, Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlas i))
    (targetOpen : cover.I₀ → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (affine i).hom ⊆ targetOpen i) :
    (ofFamily cover affine isAffine atlas etale locallySurjective
        targetOpen isAffineOpen_targetOpen range_subset_targetOpen).affine =
      affine :=
  rfl

/-- The atlas family of `ofFamily` is the given family of morphisms. -/
@[simp]
theorem ofFamily_atlas (cover : ZariskiCover X) (affine : cover.I₀ → Over S)
    (isAffine : ∀ i, IsAffine (affine i).left)
    (atlas : ∀ i, ofOver (affine i) ⟶ cover.X i)
    (etale : ∀ i, (MorphismProperty.over (@Etale)).presheaf (atlas i))
    (locallySurjective :
      ∀ i, Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlas i))
    (targetOpen : cover.I₀ → S.Opens)
    (isAffineOpen_targetOpen : ∀ i, IsAffineOpen (targetOpen i))
    (range_subset_targetOpen : ∀ i, Set.range (affine i).hom ⊆ targetOpen i) :
    (ofFamily cover affine isAffine atlas etale locallySurjective
        targetOpen isAffineOpen_targetOpen range_subset_targetOpen).atlas =
      atlas :=
  rfl

/-- An affine étale Zariski cover is a Zariski covering whose members each admit a single
affine étale locally surjective atlas mapping into an affine open of `S`. -/
theorem spec (𝒰 : AffineEtaleZariskiCover X) :
    (∀ i, IsOpenImmersion (𝒰.cover.f i)) ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) 𝒰.cover.coverSheafHom ∧
      ∀ i,
        IsAffine (𝒰.affine i).left ∧
          (MorphismProperty.over (@Etale)).presheaf (𝒰.atlas i) ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (𝒰.atlas i) ∧
          IsAffineOpen (𝒰.targetOpen i) ∧
          Set.range (𝒰.affine i).hom ⊆ 𝒰.targetOpen i :=
  ⟨𝒰.cover.isOpenImmersion, 𝒰.cover.covers, fun i ↦
    ⟨𝒰.isAffine i, 𝒰.etale i, 𝒰.locallySurjective i,
      𝒰.isAffineOpen_targetOpen i, 𝒰.range_subset_targetOpen i⟩⟩

/-- The composite atlas of the `i`-th affine scheme into `X`. -/
def atlasHom (𝒰 : AffineEtaleZariskiCover X) (i : 𝒰.cover.I₀) :
    ofOver (𝒰.affine i) ⟶ X :=
  𝒰.atlas i ≫ 𝒰.cover.f i

/-- `atlasHom 𝒰 i` is the composite of the piece atlas with the open immersion. -/
theorem atlasHom_eq (𝒰 : AffineEtaleZariskiCover X) (i : 𝒰.cover.I₀) :
    𝒰.atlasHom i = 𝒰.atlas i ≫ 𝒰.cover.f i :=
  rfl

/-- Every `T`-point of the `i`-th open subspace has structure morphism landing in the chosen
affine open of `S`. -/
theorem mapsInto_targetOpen (𝒰 : AffineEtaleZariskiCover X) (i : 𝒰.cover.I₀) {T : Over S}
    (x : (𝒰.cover.X i).functorOfPoints.obj (op T)) :
    Set.range T.hom ⊆ 𝒰.targetOpen i := by
  have hs : Sieve.overEquiv T (Presheaf.imageSieve (𝒰.atlas i) x) ∈
      Scheme.etaleTopology T.left :=
    (𝒰.locallySurjective i).imageSieve_mem x
  obtain ⟨𝒱, h𝒱⟩ := Scheme.mem_grothendieckTopology_iff.mp hs
  rintro _ ⟨t, rfl⟩
  obtain ⟨j, y, hy⟩ := 𝒱.exists_eq t
  let U : Over S := Over.mk (𝒱.f j ≫ T.hom)
  let g : U ⟶ T := Over.homMk (𝒱.f j)
  obtain ⟨a, _⟩ : Presheaf.imageSieve (𝒰.atlas i) x g :=
    (Sieve.overEquiv_iff _ _).mp (h𝒱 _ _ ⟨j⟩)
  have ha : T.hom t = (𝒰.affine i).hom (a.left y) := by
    rw [← hy]
    change (𝒱.f j ≫ T.hom) y = (a.left ≫ (𝒰.affine i).hom) y
    exact congrArg (fun f : 𝒱.X j ⟶ S ↦ f y) (Over.w a).symm
  rw [ha]
  exact 𝒰.range_subset_targetOpen i ⟨a.left y, rfl⟩

end AffineEtaleZariskiCover

/-- Every algebraic space over a scheme `S` admits a Zariski covering by open subspaces each
having a surjective étale atlas from a single affine scheme over `S`, which may be taken to
map into an affine open of `S`. -/
theorem exists_affineEtaleZariskiCover (X : AlgebraicSpace S) :
    Nonempty (AffineEtaleZariskiCover.{u} X) :=
  sorry

/-- From a coproduct affine étale atlas, the étale images of the summands yield an affine
étale Zariski covering. -/
theorem exists_of_affineEtaleCover {X : AlgebraicSpace S} (𝒰 : AffineEtaleCover X) :
    Nonempty (AffineEtaleZariskiCover.{u} X) :=
  exists_affineEtaleZariskiCover X

end AlgebraicGeometry.AlgebraicSpace
