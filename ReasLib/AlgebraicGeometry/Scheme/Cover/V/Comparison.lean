/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Refinement
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.Stability

/-!
# Comparison maps into valuative covering families

The common geometric cover notions used by the project each induce a `V`
covering family.  Keeping these bridges together lets later site and sheaf
arguments import one neutral comparison leaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable {T : Scheme.{u}} {ι : Type v}

/-- Every fpqc-covering indexed family is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_fpqcCovering (family : ι → Over T)
    (hfamily : Scheme.FpqcCovering family) :
    IsVCovering T (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := by
  intro U
  let Uι : (U : T.Opens).toScheme ⟶ T := (U : T.Opens).ι
  let pulled : ι → Over (U : T.Opens).toScheme :=
    fun i ↦ Over.mk (pullback.snd (family i).hom Uι)
  have hpulled : Scheme.FpqcCovering pulled :=
    SemiRepresentableFamily.Over.IsCovering.baseChange hfamily Uι
  let 𝒰 : FpqcCover (U : T.Opens).toScheme :=
    { I₀ := ι
      X := fun i ↦ (pulled i).left
      f := fun i ↦ (pulled i).hom
      mem₀ := hpulled }
  obtain ⟨𝒱, φ, hφ⟩ := FpqcCover.exists_standardRefinement 𝒰
  refine ⟨𝒱.toAffineFamily, StandardFpqcCover.isStandardVCover 𝒱, ?_⟩
  let chart : Fin 𝒱.n → ι := fun j ↦ φ.α j
  refine ⟨chart, ?_⟩
  intro j
  refine ⟨(φ.f j).left, ?_⟩
  change (φ.f j).left ≫ pullback.snd (family (chart j)).hom Uι = 𝒱.map j
  simpa [chart, pulled, 𝒰] using Over.w (φ.f j)

/-- Every fixed-target fppf cover is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_fppfCover (cover : FppfCover T) :
    IsVCovering T cover.X cover.f := by
  exact isVCovering_of_fpqcCovering (fun i ↦ Over.mk (cover.f i))
    (cover.weaken Scheme.fppfPrecoverage_le_fpqcPrecoverage).mem₀

/-- Every fixed-target syntomic cover is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_syntomicCover (cover : SyntomicCover T) :
    IsVCovering T cover.X cover.f := by
  have hle : Scheme.precoverage @Syntomic ≤ Scheme.fppfPrecoverage :=
    Scheme.precoverage_mono fun X Y f hf ↦ by
      letI := hf
      exact ⟨inferInstance, inferInstance⟩
  exact isVCovering_of_fpqcCovering (fun i ↦ Over.mk (cover.f i))
    ((cover.weaken (le_trans hle Scheme.fppfPrecoverage_le_fpqcPrecoverage)).mem₀)

/-- Every smooth-covering indexed family is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_smoothCovering
    (family : ι → Over T) (hfamily : Scheme.SmoothCovering family) :
    IsVCovering T (fun i ↦ (family i).left) (fun i ↦ (family i).hom) := by
  have hle : Scheme.precoverage @Smooth ≤ Scheme.fppfPrecoverage :=
    Scheme.precoverage_mono fun X Y f hf ↦ by
      letI := hf
      exact ⟨inferInstance, inferInstance⟩
  exact isVCovering_of_fpqcCovering family
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ (hle _ hfamily))

/-- Every étale cover is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_etaleCovering (cover : Scheme.Cover Scheme.etalePrecoverage T) :
    IsVCovering T cover.X cover.f := by
  have hle : Scheme.etalePrecoverage ≤ Scheme.fppfPrecoverage :=
    Scheme.precoverage_mono fun X Y f hf ↦ by
      letI := hf
      exact ⟨inferInstance, inferInstance⟩
  exact isVCovering_of_fpqcCovering (fun i ↦ Over.mk (cover.f i))
    ((cover.weaken (le_trans hle Scheme.fppfPrecoverage_le_fpqcPrecoverage)).mem₀)

/-- Every Zariski open cover is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_zariskiCovering (cover : T.OpenCover) :
    IsVCovering T cover.X cover.f := by
  exact isVCovering_of_fpqcCovering (fun i ↦ Over.mk (cover.f i))
    (cover.weaken Scheme.zariskiPrecoverage_le_fpqcPrecoverage).mem₀

/-- Every proper-hypercovering family is a `V` cover. -/
@[stacks 0ETK]
theorem isVCovering_of_phCovering {family : ι → Scheme.{u}}
    {map : ∀ i, family i ⟶ T} (hfamily : PhCovering family map) :
    IsVCovering T family map := by
  classical
  intro U
  obtain ⟨𝒱, h𝒱⟩ := hfamily.refinesOnAffineOpens U
  refine ⟨𝒱.toAffineFamily, StandardPhCovering.isStandardVCover 𝒱, ?_⟩
  choose chart lift hlift using h𝒱
  exact ⟨chart, fun j ↦ ⟨lift j, hlift j⟩⟩

/-- A fixed-target family of locally finitely presented scheme morphisms is a
proper-hypercovering family if and only if it is a `V` covering family. -/
theorem phCovering_iff_isVCovering_of_locallyOfFinitePresentation
    {ι : Type v} {T : Scheme.{u}} (family : ι → Scheme.{u})
    (map : ∀ i, family i ⟶ T)
    (hmap : ∀ i, LocallyOfFinitePresentation (map i)) :
    PhCovering family map ↔ IsVCovering T family map := by
  constructor
  · exact isVCovering_of_phCovering
  · intro hfamily
    -- Stacks 0ETR uses generic flatness stratification and flattening by admissible blowups.
    sorry

end AlgebraicGeometry
