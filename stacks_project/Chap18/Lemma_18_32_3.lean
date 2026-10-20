module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InvertiblePullback
import StacksCheckRecall

/-!
# Lemma 18.32.3

Pullback preservation of invertibility is the strong-monoidal image theorem, registered for
module-sheaf pullback in ReasLib.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable (F : D ⥤ C) [F.IsContinuous JD JC]
variable {OC : Sheaf JC CommRingCat.{u}} {OD : Sheaf JD CommRingCat.{u}}
variable
  (phi : ringSheaf JD OD ⟶
    (F.sheafPushforwardContinuous RingCat.{u} JD JC).obj (ringSheaf JC OC))
variable [(SheafOfModules.pushforward phi).IsRightAdjoint]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JD AddCommGrpCat.{u}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(SheafOfModules.pullback phi).Monoidal]
variable (L : ringedSiteModuleCategory JD OD)

/- Lemma 18.32.3 (0B8P): pullback preserves invertible module sheaves. -/
@[stacks 0B8P]
#check fun [MonoidalCategory.isInvertibleObject L] ↦
  (pullback_isInvertible F phi L :
    MonoidalCategory.isInvertibleObject ((SheafOfModules.pullback phi).obj L))

end SheafOfModules.RingedSite
