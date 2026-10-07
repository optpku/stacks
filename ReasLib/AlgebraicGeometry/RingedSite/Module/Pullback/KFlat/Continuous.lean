module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Stalk
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Continuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat pullback from a continuous presentation

Enough points on the output site detect K-flatness, so the stalkwise base-change argument shows
that continuous-presentation pullback preserves K-flat complexes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace SheafOfModules.RingedSite.modulePullbackComplex

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [GrothendieckTopology.HasEnoughPoints.{w} JY]
variable (F : C ⥤ D) [F.IsContinuous JX JY]
variable (φ : OX ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} JX JY).obj OY)
variable [(SheafOfModules.pushforward.{w} (moduleStructureMap F φ)).IsRightAdjoint]

/-- Lemma 21.18.7, continuous-presentation form: when the output site has enough points,
module pullback preserves K-flat cochain complexes. -/
@[stacks 0DEP "continuous presentation"]
theorem isKFlat_of_hasEnoughPoints
    {K : CochainComplex (ringedSiteModuleCategory.{uX, vX, w, w} JX OX) ℤ}
    (hK : K.IsKFlat) :
    ((modulePullbackComplex F φ).obj K).IsKFlat := sorry

end SheafOfModules.RingedSite.modulePullbackComplex
