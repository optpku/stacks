/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Flat

@[expose] public section

open CategoryTheory CategoryTheory.Limits
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
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable {π : O' ⟶ O} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O)

/-- In a strict square of first-order thickenings with flat thickened structure map,
the comparison from the pulled-back base ideal to the source ideal is invertible. -/
instance kernelPullbackMap_isIso
    [hstrict : Epi (kernelPullbackMap f f' hcomm)]
    [hflat : IsFlat OB' ((restrictionAlong f').obj (unitModule J O'))] :
    IsIso (kernelPullbackMap f f' hcomm) := sorry

/-- Tensoring the ideal comparison of a strict flat square with a module is invertible. -/
instance moduleTensor_kernelPullback_isIso
    [hstrict : Epi (kernelPullbackMap f f' hcomm)]
    [hflat : IsFlat OB' ((restrictionAlong f').obj (unitModule J O'))] :
    IsIso (moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 F)) := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
