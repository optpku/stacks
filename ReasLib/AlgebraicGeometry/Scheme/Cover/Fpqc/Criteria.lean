/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc

/-!
# Local criteria for fpqc covering families

This leaf separates the local image-cover conditions that occur in equivalent
characterizations of fpqc covers.  The canonical topology owner remains
`Scheme.FpqcCovering`; the predicates below are deliberately fine-grained so
they can also be reused in arguments about local refinements.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme
namespace Fpqc
namespace Criterion

variable {T : Scheme.{u}} {ι : Type v}

/-- A family of quasi-compact opens in the members of `X` has image exactly
the open subset `U` of the target. -/
def imageCover (X : ι → Over T) (U : T.Opens) : Prop :=
  ∃ V : (i : ι) → (X i).left.Opens,
    Set.Finite {i : ι | V i ≠ ⊥} ∧
      (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
        (⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)) = (U : Set T)

/-- Every member of an indexed family over `T` is flat. -/
def pointwiseFlat (X : ι → Over T) : Prop :=
  ∀ i : ι, Flat (X i).hom

/-- The local image-cover condition on every affine open of the target. -/
def Affine (X : ι → Over T) : Prop :=
  pointwiseFlat X ∧
    ∀ U : T.Opens, IsAffineOpen U → imageCover X U

/-- A family satisfying the affine criterion is pointwise flat. -/
theorem Affine.flat {X : ι → Over T} (hX : Affine X) (i : ι) :
    Flat (X i).hom := hX.1 i

/-- The affine criterion supplies an image cover of every affine target
open. -/
theorem Affine.imageCover {X : ι → Over T} (hX : Affine X)
    (U : T.Opens) (hU : IsAffineOpen U) :
    imageCover X U := hX.2 U hU

/-- The local image-cover criterion checked on one affine open cover of the
target. -/
def Refinement (X : ι → Over T) : Prop :=
  pointwiseFlat X ∧
    ∃ 𝒰 : Scheme.AffineOpenCover.{u} T,
      ∀ a : 𝒰.I₀, imageCover X ((𝒰.f a).opensRange)

/-- A family satisfying the affine-cover refinement criterion is pointwise
flat. -/
theorem Refinement.flat {X : ι → Over T} (hX : Refinement X) (i : ι) :
    Flat (X i).hom := hX.1 i

/-- The refinement criterion supplies an affine open cover with an image
cover on every member. -/
theorem Refinement.cover {X : ι → Over T} (hX : Refinement X) :
    ∃ 𝒰 : Scheme.AffineOpenCover.{u} T,
      ∀ a : 𝒰.I₀, imageCover X ((𝒰.f a).opensRange) := hX.2

/-- The local image-cover condition in a neighborhood of one target point. -/
def neighborhoodCover (X : ι → Over T) (t : T) : Prop :=
  ∃ V : (i : ι) → (X i).left.Opens,
    Set.Finite {i : ι | V i ≠ ⊥} ∧
      (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
        ∃ W : T.Opens,
          t ∈ (W : Set T) ∧
            (W : Set T) ⊆
              ⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)

/-- The pointwise local image-cover criterion. -/
def Neighborhood (X : ι → Over T) : Prop :=
  pointwiseFlat X ∧ ∀ t : T, neighborhoodCover X t

/-- A family satisfying the neighborhood criterion is pointwise flat. -/
theorem Neighborhood.flat {X : ι → Over T} (hX : Neighborhood X) (i : ι) :
    Flat (X i).hom := hX.1 i

/-- The neighborhood criterion supplies a local image cover at every target
point. -/
theorem Neighborhood.atPoint {X : ι → Over T} (hX : Neighborhood X) (t : T) :
    neighborhoodCover X t := hX.2 t

private theorem imageCover_iff_isCompactOpenCovered (X : ι → Over T) (U : T.Opens) :
    imageCover X U ↔ IsCompactOpenCovered (fun i ↦ (X i).hom) (U : Set T) := by
  classical
  constructor
  · rintro ⟨V, hf, hc, heq⟩
    refine ⟨{i | V i ≠ ⊥}, hf, fun i _ ↦ V i, fun i _ ↦ hc i, ?_⟩
    rw [← heq]
    ext t
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, _, ht⟩
      exact ⟨i, ht⟩
    · rintro ⟨i, y, hy, rfl⟩
      refine ⟨i, ?_, y, hy, rfl⟩
      intro hi
      simpa [hi] using hy
  · rintro ⟨s, hs, V, hc, heq⟩
    let W : (i : ι) → (X i).left.Opens := fun i ↦ if hi : i ∈ s then V i hi else ⊥
    refine ⟨W, hs.subset ?_, ?_, ?_⟩
    · intro i hi
      by_contra his
      exact hi (by simp [W, his])
    · intro i
      by_cases hi : i ∈ s
      · simpa [W, hi] using hc i hi
      · simp [W, hi]
    · rw [← heq]
      ext t
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, ht⟩
        by_cases hi : i ∈ s
        · exact ⟨i, hi, by simpa [W, hi] using ht⟩
        · simpa [W, hi] using ht
      · rintro ⟨i, hi, ht⟩
        exact ⟨i, by simpa [W, hi] using ht⟩

private theorem isCompact_inf_preimage {Y : Scheme.{u}} (f : Y ⟶ T)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) [QuasiSeparatedSpace T]
    (W : T.Opens) (hW : IsCompact (W : Set T)) :
    IsCompact (V ⊓ f ⁻¹ᵁ W : Set Y) := by
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have hc := (V.ι ≫ f).isCompact_preimage hW
  convert hc.image V.ι.continuous using 1
  ext y
  change (y ∈ V ∧ f y ∈ W) ↔ ∃ x : V, f x ∈ W ∧ (x : Y) = y
  constructor
  · rintro ⟨hy, hw⟩
    exact ⟨⟨y, hy⟩, hw, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

private theorem isCompact_inf_preimage_of_isAffineOpen {Y : Scheme.{u}} (f : Y ⟶ T)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) (U : T.Opens) (hU : IsAffineOpen U)
    (W : T.Opens) (hW : IsCompact (W : Set T))
    (hVU : V ≤ f ⁻¹ᵁ U) (hWU : W ≤ U) :
    IsCompact (V ⊓ f ⁻¹ᵁ W : Set Y) := by
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV
  letI : IsAffine U.toScheme := hU
  have hcW : IsCompact (U.ι ⁻¹ᵁ W : Set U) :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.isCompact_preimage' hW
      (by simpa using hWU)
  have hc := (f.resLE U V hVU).isCompact_preimage hcW
  convert hc.image V.ι.continuous using 1
  ext y
  change (y ∈ V ∧ f y ∈ W) ↔
    ∃ x : V, (f.resLE U V hVU x).1 ∈ W ∧ (x : Y) = y
  simp only [Scheme.Hom.coe_resLE_apply]
  constructor
  · rintro ⟨hy, hw⟩
    exact ⟨⟨y, hy⟩, hw, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

private theorem imageCover_of_restriction (X : ι → Over T) (U : T.Opens)
    (V : (i : ι) → (X i).left.Opens) (hf : Set.Finite {i | V i ≠ ⊥})
    (hc : ∀ i, IsCompact (V i ⊓ (X i).hom ⁻¹ᵁ U : Set (X i).left))
    (hcov : (U : Set T) ⊆ ⋃ i, (X i).hom.base '' (V i : Set (X i).left)) :
    imageCover X U := by
  refine ⟨fun i ↦ V i ⊓ (X i).hom ⁻¹ᵁ U, hf.subset ?_, hc, ?_⟩
  · intro i hi heq
    exact hi (by simp [heq])
  · ext t
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨i, y, hy, rfl⟩
      exact hy.2
    · intro ht
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp (hcov ht)
      exact ⟨i, y, ⟨hy, ht⟩, rfl⟩

/-- The canonical fpqc-covering predicate is characterized by the affine
local image-cover criterion. -/
theorem cover_iff_affine (X : ι → Over T) :
    FpqcCovering X ↔ Affine X := by
  let E : PreZeroHypercover.{v} T :=
    { I₀ := ι
      X i := (X i).left
      f i := (X i).hom }
  change E.presieve₀ ∈ fpqcPrecoverage T ↔ Affine X
  change (E.presieve₀ ∈ qcPrecoverage T ∧ E.presieve₀ ∈ precoverage @Flat T) ↔ Affine X
  rw [presieve₀_mem_qcPrecoverage_iff, presieve₀_mem_precoverage_iff]
  constructor
  · rintro ⟨hqc, _, hflat⟩
    refine ⟨hflat, fun U hU ↦ ?_⟩
    exact (imageCover_iff_isCompactOpenCovered X U).mpr
      (hqc.isCompactOpenCovered_of_isAffineOpen hU)
  · intro hX
    refine ⟨⟨fun {U} hU ↦ (imageCover_iff_isCompactOpenCovered X U).mp (hX.2 U hU)⟩,
      ?_, hX.1⟩
    intro t
    obtain ⟨U, hU, ht, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      T.isBasis_affineOpens (TopologicalSpace.Opens.mem_top t)
    obtain ⟨V, _, _, hV⟩ := hX.2 U hU
    have ht' : t ∈ ⋃ i, (X i).hom.base '' (V i : Set (X i).left) := hV.symm ▸ ht
    obtain ⟨i, y, _, hy⟩ := Set.mem_iUnion.mp ht'
    exact ⟨i, y, hy⟩

/-- The affine local criterion is equivalent to the affine-cover refinement
criterion. -/
theorem affine_iff_refinement (X : ι → Over T) :
    Affine X ↔ Refinement X := by
  constructor
  · intro hX
    exact ⟨hX.1, T.affineOpenCover,
      fun a ↦ hX.2 _ (isAffineOpen_opensRange (T.affineOpenCover.f a))⟩
  · rintro ⟨hflat, 𝒰, h𝒰⟩
    refine ⟨hflat, fun U hU ↦ (imageCover_iff_isCompactOpenCovered X U).mpr ?_⟩
    apply IsCompactOpenCovered.of_isCompact_of_forall_exists_isCompactOpenCovered hU.isCompact
    intro t htU
    let a := 𝒰.idx t
    let A := (𝒰.f a).opensRange
    have htA : t ∈ A := 𝒰.covers t
    obtain ⟨W, hW, htW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      T.isBasis_affineOpens (show t ∈ A ⊓ U from ⟨htA, htU⟩)
    obtain ⟨V, hf, hc, hcov⟩ := h𝒰 a
    have hVA (i : ι) : V i ≤ (X i).hom ⁻¹ᵁ A := by
      intro y hy
      have h : (X i).hom y ∈ ⋃ i, (X i).hom.base '' (V i : Set (X i).left) :=
        Set.mem_iUnion.mpr ⟨i, y, hy, rfl⟩
      rw [hcov] at h
      exact h
    refine ⟨(W : Set T), hWle.trans inf_le_right, htW, W.isOpen,
      (imageCover_iff_isCompactOpenCovered X W).mp ?_⟩
    apply imageCover_of_restriction X W V hf
    · intro i
      exact isCompact_inf_preimage_of_isAffineOpen (X i).hom (V i) (hc i) A
        (isAffineOpen_opensRange (𝒰.f a)) W hW.isCompact (hVA i) (hWle.trans inf_le_left)
    · rw [hcov]
      exact hWle.trans inf_le_left

/-- On a quasi-separated target, the affine local criterion is equivalent to
the pointwise neighborhood criterion. -/
theorem affine_iff_neighborhood (X : ι → Over T) [QuasiSeparatedSpace T] :
    Affine X ↔ Neighborhood X := by
  constructor
  · intro hX
    refine ⟨hX.1, fun t ↦ ?_⟩
    obtain ⟨U, hU, ht, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      T.isBasis_affineOpens (TopologicalSpace.Opens.mem_top t)
    obtain ⟨V, hf, hc, hcov⟩ := hX.2 U hU
    exact ⟨V, hf, hc, U, ht, hcov.ge⟩
  · intro hX
    refine ⟨hX.1, fun U hU ↦ (imageCover_iff_isCompactOpenCovered X U).mpr ?_⟩
    apply IsCompactOpenCovered.of_isCompact_of_forall_exists_isCompactOpenCovered hU.isCompact
    intro t htU
    obtain ⟨V, hf, hc, A, htA, hcov⟩ := hX.2 t
    obtain ⟨W, hW, htW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      T.isBasis_affineOpens (show t ∈ A ⊓ U from ⟨htA, htU⟩)
    refine ⟨(W : Set T), hWle.trans inf_le_right, htW, W.isOpen,
      (imageCover_iff_isCompactOpenCovered X W).mp ?_⟩
    apply imageCover_of_restriction X W V hf
    · intro i
      exact isCompact_inf_preimage (X i).hom (V i) (hc i) W hW.isCompact
    · intro t ht
      exact hcov ((hWle ht).1)

end Criterion
end Fpqc
end AlgebraicGeometry.Scheme
