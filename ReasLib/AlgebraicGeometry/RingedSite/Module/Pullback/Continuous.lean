/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module pullback from a continuous presentation

A continuous functor of sites together with an inverse-image-form structure-ring map determines
direct and inverse image functors on sheaves of modules.  This presentation layer does not impose
the representable-flatness hypothesis carried by `RingedSite.Hom`.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe uX vX uY vY w z

namespace SheafOfModules.RingedSite

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable (F : C ⥤ D) [F.IsContinuous JX JY]
variable (φ : OX ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} JX JY).obj OY)

/-- The underlying morphism of ring sheaves associated to a continuous commutative-ringed
presentation. -/
@[stacks 03D6 "continuous presentation"]
def moduleStructureMap :
    ringSheaf JX OX ⟶
      (F.sheafPushforwardContinuous RingCat.{w} JX JY).obj (ringSheaf JY OY) :=
  (sheafCompose JX (forget₂ CommRingCat.{w} RingCat.{w})).map φ

/-- Direct image of module sheaves associated to a continuous presentation. -/
@[stacks 03D6 "(1), continuous presentation"]
noncomputable abbrev modulePushforward :
    ringedSiteModuleCategory.{uY, vY, z, w} JY OY ⥤
      ringedSiteModuleCategory.{uX, vX, z, w} JX OX :=
  SheafOfModules.pushforward.{z} (moduleStructureMap F φ)

/-- Inverse image of module sheaves associated to a continuous presentation. -/
@[stacks 03D6 "(2), continuous presentation"]
noncomputable abbrev modulePullback
    [(SheafOfModules.pushforward.{z} (moduleStructureMap F φ)).IsRightAdjoint] :
    ringedSiteModuleCategory.{uX, vX, z, w} JX OX ⥤
      ringedSiteModuleCategory.{uY, vY, z, w} JY OY :=
  SheafOfModules.pullback.{z} (moduleStructureMap F φ)

/-- Module pullback from a continuous presentation is additive. -/
instance modulePullback_additive
    [HasWeakSheafify JY AddCommGrpCat.{z}]
    [JY.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [(SheafOfModules.pushforward.{z} (moduleStructureMap F φ)).IsRightAdjoint] :
    (modulePullback F φ :
      ringedSiteModuleCategory.{uX, vX, z, w} JX OX ⥤
        ringedSiteModuleCategory.{uY, vY, z, w} JY OY).Additive := sorry

/-- Module pullback from a continuous presentation applied degreewise to unbounded cochain
complexes. -/
@[stacks 0G7E "continuous presentation"]
noncomputable abbrev modulePullbackComplex
    [HasWeakSheafify JY AddCommGrpCat.{z}]
    [JY.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [(SheafOfModules.pushforward.{z} (moduleStructureMap F φ)).IsRightAdjoint] :
    CochainComplex (ringedSiteModuleCategory.{uX, vX, z, w} JX OX) ℤ ⥤
      CochainComplex (ringedSiteModuleCategory.{uY, vY, z, w} JY OY) ℤ :=
  (modulePullback F φ).mapHomologicalComplex (up ℤ)

namespace modulePullbackComplex

/-- In each degree, continuous-presentation pullback is the corresponding module pullback. -/
@[simp]
theorem obj_X
    [HasWeakSheafify JY AddCommGrpCat.{z}]
    [JY.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [(SheafOfModules.pushforward.{z} (moduleStructureMap F φ)).IsRightAdjoint]
    (K : CochainComplex (ringedSiteModuleCategory.{uX, vX, z, w} JX OX) ℤ) (n : ℤ) :
    ((modulePullbackComplex F φ).obj K).X n =
      (modulePullback F φ).obj (K.X n) := sorry

end modulePullbackComplex
end SheafOfModules.RingedSite
