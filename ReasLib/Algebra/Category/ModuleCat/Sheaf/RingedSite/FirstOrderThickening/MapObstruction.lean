/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Obstruction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Lift

set_option backward.privateInPublic true

/-!
# Relative Ext obstruction for a map along a strict first-order thickening

A strict morphism of first-order thickenings and a map between the reductions of two
flat modules determine a canonical obstruction class in the corresponding Ext group.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable (π : O' ⟶ O) {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)

/-- The source-ideal inclusion followed by the reduction projection is zero. -/
private theorem ofSourceIdealMul_zero
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
    [IsFlat OB' ((restrictionAlong f').obj F')] (hstrict : IsStrict f f' hcomm) :
    ((restrictionAlong π).map (canonicalMap π f f' hcomm F') ≫ (ofPullback π F').ι) ≫
        (ofPullback π F').p = 0 := sorry

/-- The source-ideal inclusion and projection form a short exact sequence. -/
private theorem ofSourceIdealMul_shortExact
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
    [IsFlat OB' ((restrictionAlong f').obj F')] (hstrict : IsStrict f f' hcomm) :
    (ShortComplex.mk
        ((restrictionAlong π).map (canonicalMap π f f' hcomm F') ≫ (ofPullback π F').ι)
        (ofPullback π F').p (ofSourceIdealMul_zero π f f' hcomm F' hstrict)).ShortExact := sorry

/-- The source-ideal extension associated to a strict square and a flat module. -/
def ofSourceIdealMul (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
    [IsFlat OB' ((restrictionAlong f').obj F')] (hstrict : IsStrict f f' hcomm) :
    Extension π where
  kernel :=
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
      ((extendScalars (ringSheafMap π)).obj F')
  middle := F'
  quot := (extendScalars (ringSheafMap π)).obj F'
  ι := (restrictionAlong π).map (canonicalMap π f f' hcomm F') ≫
    (ofPullback π F').ι
  p := (ofPullback π F').p
  zero := ofSourceIdealMul_zero π f f' hcomm F' hstrict
  shortExact := ofSourceIdealMul_shortExact π f f' hcomm F' hstrict

/-- The data fields of the source-ideal extension. -/
theorem ofSourceIdealMul_spec
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
    [IsFlat OB' ((restrictionAlong f').obj F')] (hstrict : IsStrict f f' hcomm) :
    (ofSourceIdealMul π f f' hcomm F' hstrict).kernel =
        moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
          ((extendScalars (ringSheafMap π)).obj F') ∧
      (ofSourceIdealMul π f f' hcomm F' hstrict).middle = F' ∧
      (ofSourceIdealMul π f f' hcomm F' hstrict).quot =
        (extendScalars (ringSheafMap π)).obj F' ∧
      (ofSourceIdealMul π f f' hcomm F' hstrict).ι =
        (restrictionAlong π).map (canonicalMap π f f' hcomm F') ≫
          (ofPullback π F').ι ∧
      (ofSourceIdealMul π f f' hcomm F' hstrict).p = (ofPullback π F').p := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The endpoint maps of two source-ideal extensions satisfy the infinitesimal square. -/
private theorem sourceIdealMul_infMapCommSq
    {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    [IsFlat OB' ((restrictionAlong f').obj F')]
    [IsFlat OB' ((restrictionAlong f').obj G')]
    (hstrict : IsStrict f f' hcomm)
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    infMapCommSq (ofSourceIdealMul π f f' hcomm F' hstrict)
      (ofSourceIdealMul π f f' hcomm G' hstrict) φ
      (moduleTensorMap (𝟙 ((extendScalars (ringSheafMap f)).obj (ideal τ))) φ) := sorry

variable [HasExt (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]

/-- The canonical Ext¹ obstruction class for a map between reductions of flat modules. -/
noncomputable def obstruction {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    [IsFlat OB' ((restrictionAlong f').obj F')]
    [IsFlat OB' ((restrictionAlong f').obj G')]
    (hstrict : IsStrict f f' hcomm)
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    Ext ((extendScalars (ringSheafMap π)).obj F')
      (moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj G')) 1 :=
  mapObstruction (ofSourceIdealMul π f f' hcomm F' hstrict)
    (ofSourceIdealMul π f f' hcomm G' hstrict) φ
    (moduleTensorMap (𝟙 ((extendScalars (ringSheafMap f)).obj (ideal τ))) φ)
    (sourceIdealMul_infMapCommSq π f f' hcomm hstrict φ)

/-- The obstruction is the mixed-scalar extension obstruction of its endpoint maps. -/
theorem obstruction_eq {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    [IsFlat OB' ((restrictionAlong f').obj F')]
    [IsFlat OB' ((restrictionAlong f').obj G')]
    (hstrict : IsStrict f f' hcomm)
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    obstruction π f f' hcomm hstrict φ =
      mapObstruction (ofSourceIdealMul π f f' hcomm F' hstrict)
        (ofSourceIdealMul π f f' hcomm G' hstrict) φ
        (moduleTensorMap (𝟙 ((extendScalars (ringSheafMap f)).obj (ideal τ))) φ)
        (sourceIdealMul_infMapCommSq π f f' hcomm hstrict φ) := rfl

/-- The relative obstruction vanishes exactly when the map admits a lift. -/
theorem obstruction_eq_zero_iff {F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'}
    [IsFlat OB' ((restrictionAlong f').obj F')]
    [IsFlat OB' ((restrictionAlong f').obj G')]
    (hstrict : IsStrict f f' hcomm)
    (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
      (extendScalars (ringSheafMap π)).obj G') :
    obstruction π f f' hcomm hstrict φ = 0 ↔ Nonempty (Lift F' G' φ) := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
