module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineEtaleZariskiCover
public import Mathlib.Data.List.TFAE

/-!
# Characterizations of Zariski-local quasi-separatedness

Relative Zariski-local quasi-separatedness of an algebraic space is equivalent to the absolute
notion, and to the existence of a Zariski covering by open subspaces each admitting a
quasi-compact surjective étale atlas from an affine scheme, optionally mapping into an affine
open of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- An algebraic space admits a Zariski covering by open subspaces each having a quasi-compact
surjective étale morphism from an affine scheme. -/
def HasQuasiCompactAffineEtaleZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} X) (U : 𝒰.I₀ → Over S) (φ : ∀ i, ofOver (U i) ⟶ 𝒰.X i),
    ∀ i, IsAffine (U i).left ∧
      (MorphismProperty.over (@Etale)).presheaf (φ i) ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (φ i) ∧
      (MorphismProperty.over (@QuasiCompact)).presheaf (φ i)

/-- An algebraic space admits a Zariski covering by open subspaces each having a quasi-compact
surjective étale morphism from an affine scheme mapping into an affine open of the base. -/
def HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase : Prop :=
  ∃ 𝒰 : AffineEtaleZariskiCover.{u} X,
    ∀ i, (MorphismProperty.over (@QuasiCompact)).presheaf (𝒰.atlas i)

/-- An algebraic space has a quasi-compact affine étale Zariski cover precisely when there is a
Zariski covering with affine, étale locally surjective, quasi-compact atlases. -/
theorem hasQuasiCompactAffineEtaleZariskiCover_iff :
    HasQuasiCompactAffineEtaleZariskiCover X ↔
      ∃ (𝒰 : ZariskiCover.{u, u} X) (U : 𝒰.I₀ → Over S) (φ : ∀ i, ofOver (U i) ⟶ 𝒰.X i),
        ∀ i, IsAffine (U i).left ∧
          (MorphismProperty.over (@Etale)).presheaf (φ i) ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (φ i) ∧
          (MorphismProperty.over (@QuasiCompact)).presheaf (φ i) :=
  Iff.rfl

/-- An algebraic space has a quasi-compact affine étale Zariski cover on an affine base precisely
when such a cover has affine, étale locally surjective, quasi-compact atlases whose structure
morphisms land in the chosen affine opens of the base. -/
theorem hasQuasiCompactAffineEtaleZariskiCoverOnAffineBase_iff :
    HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X ↔
      ∃ 𝒰 : AffineEtaleZariskiCover.{u} X,
        ∀ i, IsAffine (𝒰.affine i).left ∧
          (MorphismProperty.over (@Etale)).presheaf (𝒰.atlas i) ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (𝒰.atlas i) ∧
          (MorphismProperty.over (@QuasiCompact)).presheaf (𝒰.atlas i) ∧
          IsAffineOpen (𝒰.targetOpen i) ∧
          Set.range (𝒰.affine i).hom ⊆ 𝒰.targetOpen i := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i ↦ ⟨𝒰.isAffine i, 𝒰.etale i, 𝒰.locallySurjective i, h i,
      𝒰.isAffineOpen_targetOpen i, 𝒰.range_subset_targetOpen i⟩⟩
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i ↦ (h i).2.2.2.1⟩

/-- Forgetting the chosen affine opens of the base gives a quasi-compact affine étale Zariski
cover. -/
theorem HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase.to_hasQuasiCompactAffineEtaleZariskiCover
    (h : HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X) :
    HasQuasiCompactAffineEtaleZariskiCover X := by
  rcases h with ⟨𝒰, h⟩
  exact ⟨𝒰.cover, 𝒰.affine, 𝒰.atlas,
    fun i ↦ ⟨𝒰.isAffine i, 𝒰.etale i, 𝒰.locallySurjective i, h i⟩⟩

/-- For an algebraic space over a scheme, relative and absolute Zariski-local quasi-separatedness
are equivalent to the existence of a Zariski covering with quasi-compact surjective étale affine
atlases, optionally mapping into affine opens of the base. -/
theorem isZariskiLocallyQuasiSeparated_tfae :
    List.TFAE [IsZariskiLocallyQuasiSeparated X, IsAbsolutelyZariskiLocallyQuasiSeparated X,
      HasQuasiCompactAffineEtaleZariskiCover X,
      HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X] :=
  sorry

/-- Relative Zariski-local quasi-separatedness over `S` is equivalent to the absolute notion. -/
theorem IsZariskiLocallyQuasiSeparated.iff_absolute :
    IsZariskiLocallyQuasiSeparated X ↔ IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  (isZariskiLocallyQuasiSeparated_tfae X).out 0 1

/-- If `X` is Zariski locally quasi-separated over `S`, then it is Zariski locally
quasi-separated in the absolute sense. -/
instance IsZariskiLocallyQuasiSeparated.instAbsolute
    [h : IsZariskiLocallyQuasiSeparated X] : IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  (IsZariskiLocallyQuasiSeparated.iff_absolute X).mp h

/-- If `X` is Zariski locally quasi-separated in the absolute sense, then it is Zariski locally
quasi-separated over `S`. -/
instance (priority := 100)
    isZariskiLocallyQuasiSeparated_of_isAbsolutelyZariskiLocallyQuasiSeparated
    [h : IsAbsolutelyZariskiLocallyQuasiSeparated X] : IsZariskiLocallyQuasiSeparated X :=
  (IsZariskiLocallyQuasiSeparated.iff_absolute X).mpr h

/-- Zariski-local quasi-separatedness over `S` is equivalent to the existence of a Zariski
covering by open subspaces each having a quasi-compact surjective étale affine atlas. -/
theorem IsZariskiLocallyQuasiSeparated.iff_affineCover :
    IsZariskiLocallyQuasiSeparated X ↔ HasQuasiCompactAffineEtaleZariskiCover X :=
  (isZariskiLocallyQuasiSeparated_tfae X).out 0 2

/-- Zariski-local quasi-separatedness over `S` is equivalent to the existence of an affine étale
Zariski covering with quasi-compact atlases mapping into affine opens of `S`. -/
theorem IsZariskiLocallyQuasiSeparated.iff_affineCoverOnBase :
    IsZariskiLocallyQuasiSeparated X ↔ HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X :=
  (isZariskiLocallyQuasiSeparated_tfae X).out 0 3

/-- A Zariski locally quasi-separated algebraic space admits a Zariski covering by open subspaces
each having a quasi-compact surjective étale affine atlas. -/
theorem exists_hasQuasiCompactAffineEtaleZariskiCover [h : IsZariskiLocallyQuasiSeparated X] :
    HasQuasiCompactAffineEtaleZariskiCover X :=
  (IsZariskiLocallyQuasiSeparated.iff_affineCover X).mp h

/-- A Zariski locally quasi-separated algebraic space admits an affine étale Zariski covering with
quasi-compact atlases mapping into affine opens of the base. -/
theorem exists_hasQuasiCompactAffineEtaleZariskiCoverOnAffineBase
    [h : IsZariskiLocallyQuasiSeparated X] : HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X :=
  (IsZariskiLocallyQuasiSeparated.iff_affineCoverOnBase X).mp h

end AlgebraicGeometry.AlgebraicSpace
