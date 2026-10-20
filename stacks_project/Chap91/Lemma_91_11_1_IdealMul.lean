module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.IdealMultiple

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
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} (π : 𝒪' ⟶ 𝒪)
variable [IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]

#check (SheafOfModules.RingedSite.FirstOrderThickening.extendRestrictUnit π :
  (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') →
    M ⟶ (restrictionAlong π).obj
      ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj M))

#check (SheafOfModules.RingedSite.FirstOrderThickening.idealMulO' π :
  (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') →
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')

#check (SheafOfModules.RingedSite.FirstOrderThickening.idealMul π :
  (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') →
    ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪)

#check (SheafOfModules.RingedSite.FirstOrderThickening.unitShortComplex π :
  (M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪') →
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪'))

#check (SheafOfModules.RingedSite.FirstOrderThickening.unitShortComplex_shortExact π :
  ∀ M : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪',
    (unitShortComplex π M).ShortExact)

#check (SheafOfModules.RingedSite.FirstOrderThickening.map_kernel_bijective π :
  ∀ F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪',
    Function.Bijective fun β : F' ⟶ idealMulO' π G' ↦
      (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).map β)

end SheafOfModules.RingedSite.FirstOrderThickening
