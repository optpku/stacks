/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Lift

open CategoryTheory CategoryTheory.Limits
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
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
variable (φ : (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj G')

#check (SheafOfModules.RingedSite.FirstOrderThickening.Lift F' G' φ :
  Type (max u v))

#check (SheafOfModules.RingedSite.FirstOrderThickening.Lift.of F' G' φ :
  (hom : F' ⟶ G') →
    CommSq hom (extendRestrictUnit π F') (extendRestrictUnit π G')
      ((restrictionAlong π).map φ) → Lift F' G' φ)

#check (SheafOfModules.RingedSite.FirstOrderThickening.Lift.spec F' G' φ :
  ∀ f : Lift F' G' φ,
    CommSq f.hom (extendRestrictUnit π F') (extendRestrictUnit π G')
      ((restrictionAlong π).map φ))

#check (SheafOfModules.RingedSite.FirstOrderThickening.Lift.vadd_comm F' G' φ :
  ∀ (β : F' ⟶ idealMulO' π G') (f : Lift F' G' φ),
    (f.hom + β ≫ kernel.ι (extendRestrictUnit π G')) ≫ extendRestrictUnit π G' =
      extendRestrictUnit π F' ≫ (restrictionAlong π).map φ)

#check (SheafOfModules.RingedSite.FirstOrderThickening.Lift.vadd F' G' φ :
  (β : F' ⟶ idealMulO' π G') → (f : Lift F' G' φ) → Lift F' G' φ)

#check (SheafOfModules.RingedSite.FirstOrderThickening.Lift.vadd_hom F' G' φ :
  ∀ (β : F' ⟶ idealMulO' π G') (f : Lift F' G' φ),
    (Lift.vadd F' G' φ β f).hom = f.hom + β ≫ kernel.ι (extendRestrictUnit π G'))

#check (SheafOfModules.RingedSite.FirstOrderThickening.Lift.existsUnique_vsub F' G' φ :
  ∀ f g : Lift F' G' φ,
    ∃! α : (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
        idealMul π G',
      ∃ β : F' ⟶ idealMulO' π G',
        (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map β = α ∧
          Lift.vadd F' G' φ β g = f)

end SheafOfModules.RingedSite.FirstOrderThickening
