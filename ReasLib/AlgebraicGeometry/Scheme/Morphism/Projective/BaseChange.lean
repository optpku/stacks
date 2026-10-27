/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of projective scheme morphisms

This file collects base-change APIs for projective, H-projective, and locally projective
morphisms.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Projective morphisms are stable under arbitrary base change. -/
instance projective_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @Projective := sorry

/-- H-projective morphisms are stable under arbitrary base change. -/
instance hProjective_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @HProjective := sorry

/-- Locally projective morphisms are stable under arbitrary base change. -/
instance locallyProjective_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyProjective where
  of_isPullback {X Y Y' S} {f} {g} {f'} {g'} sq hg := by
    obtain ⟨𝒰, h𝒰⟩ := hg.exists_cover
    refine ⟨⟨X.openCoverOfIsOpenCover
      (fun i ↦ f ⁻¹ᵁ (𝒰.f i).opensRange)
      (𝒰.isOpenCover_opensRange.comap f.base.hom), ?_⟩⟩
    intro i
    change Projective (g' ∣_ (f ⁻¹ᵁ (𝒰.f i).opensRange).ι.opensRange)
    rw [Scheme.Opens.opensRange_ι]
    have hpb := Scheme.Hom.isPullback_resLE (H := sq)
      (US := (𝒰.f i).opensRange)
      (UT := f ⁻¹ᵁ (𝒰.f i).opensRange)
      (UX := g ⁻¹ᵁ (𝒰.f i).opensRange)
      (UY := g' ⁻¹ᵁ (f ⁻¹ᵁ (𝒰.f i).opensRange))
      le_rfl le_rfl (by
        simp only [← Scheme.Hom.comp_preimage, sq.w, inf_idem])
    have hprojective : Projective
        (g.resLE (𝒰.f i).opensRange (g ⁻¹ᵁ (𝒰.f i).opensRange) le_rfl) := by
      simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using h𝒰 i
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      (MorphismProperty.of_isPullback (P := @Projective) hpb hprojective)

/-- A base change of a projective morphism is projective. -/
theorem Projective.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : Projective f) (g : S' ⟶ S) :
    Projective (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/-- A base-changed projective morphism has a projective structure. -/
instance instProjectivePullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [Projective f] :
    Projective (pullback.snd f g) :=
  Projective.pullback_snd inferInstance g

/-- The pullback projection of an H-projective morphism is H-projective. -/
@[stacks 01WF]
theorem HProjective.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : HProjective f) (g : S' ⟶ S) :
    HProjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/-- A base-changed H-projective morphism has an H-projective structure. -/
instance instHProjectivePullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [HProjective f] :
    HProjective (pullback.snd f g) :=
  HProjective.pullback_snd inferInstance g

/-- A base change of a locally projective morphism is locally projective. -/
theorem LocallyProjective.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : LocallyProjective f) (g : S' ⟶ S) :
    LocallyProjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/-- A base-changed locally projective morphism has a locally projective structure. -/
instance instLocallyProjectivePullbackSnd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [LocallyProjective f] :
    LocallyProjective (pullback.snd f g) :=
  LocallyProjective.pullback_snd inferInstance g

end AlgebraicGeometry
