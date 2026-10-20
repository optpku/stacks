module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of invertible module sheaves

This is the ringed-site specialization of
`MonoidalCategory.isInvertibleObject.map`.  The named theorem lets downstream specializations
reuse the generic preservation result without rebuilding its hypotheses.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uC vC uD vD w z

namespace SheafOfModules.RingedSite

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (F : D ⥤ C) [F.IsContinuous JD JC]
variable {OC : Sheaf JC CommRingCat.{w}} {OD : Sheaf JD CommRingCat.{w}}
variable
  (phi : ringSheaf JD OD ⟶
    (F.sheafPushforwardContinuous RingCat.{w} JD JC).obj (ringSheaf JC OC))
variable [(SheafOfModules.pushforward.{z} phi).IsRightAdjoint]
variable [MonoidalCategory
  (ringedSiteModuleCategory.{uD, vD, z, w} JD OD)]
variable [MonoidalCategory
  (ringedSiteModuleCategory.{uC, vC, z, w} JC OC)]

/-- A strong monoidal module-sheaf pullback preserves invertible objects. -/
@[stacks 0B8P]
theorem pullback_isInvertible
    [(SheafOfModules.pullback.{z} phi).Monoidal]
    (L : ringedSiteModuleCategory.{uD, vD, z, w} JD OD)
    [MonoidalCategory.isInvertibleObject L] :
    MonoidalCategory.isInvertibleObject
      ((SheafOfModules.pullback.{z} phi).obj L :
        ringedSiteModuleCategory.{uC, vC, z, w} JC OC) := sorry

end SheafOfModules.RingedSite
