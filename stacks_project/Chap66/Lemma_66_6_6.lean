module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_6_2_Cover

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

/-- `HasQuasiCompactAffineEtaleZariskiCover` means there is a Zariski covering whose members each
admit a quasi-compact étale locally surjective atlas from an affine scheme. -/
theorem hasQuasiCompactAffineEtaleZariskiCover_iff :
    HasQuasiCompactAffineEtaleZariskiCover X ↔
      ∃ (𝒰 : ZariskiCover.{u, u} X) (U : 𝒰.I₀ → Over S) (φ : ∀ i, ofOver (U i) ⟶ 𝒰.X i),
        ∀ i, IsAffine (U i).left ∧
          (MorphismProperty.over (@Etale)).presheaf (φ i) ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (φ i) ∧
          (MorphismProperty.over (@QuasiCompact)).presheaf (φ i) :=
  sorry

/-- `HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase` means there is an affine étale Zariski
covering whose atlases are quasi-compact, hence map into affine opens of the base. -/
theorem hasQuasiCompactAffineEtaleZariskiCoverOnAffineBase_iff :
    HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X ↔
      ∃ 𝒰 : AffineEtaleZariskiCover.{u} X,
        ∀ i, IsAffine (𝒰.affine i).left ∧
          (MorphismProperty.over (@Etale)).presheaf (𝒰.atlas i) ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (𝒰.atlas i) ∧
          (MorphismProperty.over (@QuasiCompact)).presheaf (𝒰.atlas i) ∧
          IsAffineOpen (𝒰.targetOpen i) ∧
          Set.range (𝒰.affine i).hom ⊆ 𝒰.targetOpen i :=
  sorry

/-- A covering as in `HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase` yields a covering as in
`HasQuasiCompactAffineEtaleZariskiCover`. -/
theorem HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase.to_hasQuasiCompactAffineEtaleZariskiCover
    (h : HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X) :
    HasQuasiCompactAffineEtaleZariskiCover X :=
  sorry

/-- Lemma 66.6.6: let `S` be a scheme and `X` an algebraic space over `S`. The following are
equivalent: `X` is Zariski locally quasi-separated over `S`; `X` is Zariski locally
quasi-separated; `X` admits a Zariski covering by open subspaces each having a quasi-compact
surjective étale morphism from an affine scheme; and the same covering exists with each affine
atlas mapping into an affine open of `S`. -/
@[stacks 03W7]
theorem isZariskiLocallyQuasiSeparated_tfae :
    List.TFAE [IsZariskiLocallyQuasiSeparated X, IsAbsolutelyZariskiLocallyQuasiSeparated X,
      HasQuasiCompactAffineEtaleZariskiCover X,
      HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X] :=
  sorry

/-- If `X` is Zariski locally quasi-separated over `S`, then it is Zariski locally
quasi-separated in the absolute sense. -/
instance instIsAbsolutelyZariskiLocallyQuasiSeparated_of_isZariskiLocallyQuasiSeparated
    [IsZariskiLocallyQuasiSeparated X] : IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

/-- Relative Zariski-local quasi-separatedness over `S` is equivalent to the absolute notion. -/
theorem isZariskiLocallyQuasiSeparated_iff_isAbsolutelyZariskiLocallyQuasiSeparated :
    IsZariskiLocallyQuasiSeparated X ↔ IsAbsolutelyZariskiLocallyQuasiSeparated X :=
  sorry

/-- If `X` is Zariski locally quasi-separated in the absolute sense, then it is Zariski locally
quasi-separated over `S`. -/
theorem isZariskiLocallyQuasiSeparated_of_isAbsolutelyZariskiLocallyQuasiSeparated
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] : IsZariskiLocallyQuasiSeparated X :=
  sorry

/-- Zariski-local quasi-separatedness over `S` is equivalent to the existence of a Zariski
covering by open subspaces each having a quasi-compact surjective étale affine atlas. -/
theorem isZariskiLocallyQuasiSeparated_iff_hasQuasiCompactAffineEtaleZariskiCover :
    IsZariskiLocallyQuasiSeparated X ↔ HasQuasiCompactAffineEtaleZariskiCover X :=
  sorry

/-- Zariski-local quasi-separatedness over `S` is equivalent to the existence of an affine étale
Zariski covering with quasi-compact atlases mapping into affine opens of `S`. -/
theorem isZariskiLocallyQuasiSeparated_iff_hasQuasiCompactAffineEtaleZariskiCoverOnAffineBase :
    IsZariskiLocallyQuasiSeparated X ↔ HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X :=
  sorry

/-- A Zariski locally quasi-separated algebraic space admits a Zariski covering by open subspaces
each having a quasi-compact surjective étale affine atlas. -/
theorem exists_hasQuasiCompactAffineEtaleZariskiCover [IsZariskiLocallyQuasiSeparated X] :
    HasQuasiCompactAffineEtaleZariskiCover X :=
  sorry

/-- A Zariski locally quasi-separated algebraic space admits an affine étale Zariski covering with
quasi-compact atlases mapping into affine opens of the base. -/
theorem exists_hasQuasiCompactAffineEtaleZariskiCoverOnAffineBase
    [IsZariskiLocallyQuasiSeparated X] : HasQuasiCompactAffineEtaleZariskiCoverOnAffineBase X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
