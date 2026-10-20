/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.ExistenceObstruction

/-!
# Existence of relatively flat lifts across first-order thickenings

For a strict commutative square of first-order thickenings, a module flat over
the base admits a relatively flat lift exactly when the canonical ideal tensor
comparison is invertible and its Ext² existence obstruction vanishes.
The base ring sheaves are understood as inverse images on the source site.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable {π : O' ⟶ O} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [HasFunctorialInjectives (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [SheafOfModules.Localization.HasLowerShriek.{max u v} (ringSheaf J O')]
variable [HasExt.{w} (ringedSiteModuleCategory.{u, v, max u v, max u v} J O)]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)

/-- A module flat over the base of a strict square of first-order thickenings admits
a relatively flat lift if and only if the canonical ideal tensor comparison is invertible
and the existence obstruction with coefficient the ideal tensor module and identity
infinitesimal map vanishes. -/
theorem exists_flatOver_iff [hflat : IsFlat OB ((restrictionAlong f).obj F)]
    (hstrict : IsStrict f f' hcomm) :
    (∃ F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O',
        IsFlat OB' ((restrictionAlong f').obj F') ∧
          Nonempty ((extendScalars (ringSheafMap π)).obj F' ≅ F)) ↔
      IsIso (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F)) ∧
        ModuleExtension.existenceObstruction π F (moduleTensor (ideal π) F)
          (𝟙 (moduleTensor (ideal π) F)) = 0 := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
