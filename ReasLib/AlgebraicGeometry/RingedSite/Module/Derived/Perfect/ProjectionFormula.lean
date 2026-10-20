/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas for perfect complexes on commutative ringed sites

The geometric statement is a specialization of the categorical projection formula for a
right-dualizable object.  A coherent monoidal structure on derived pullback is kept as an
explicit data boundary until its K-flat construction has a canonical owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.ModuleDerived

set_option checkBinderAnnotations false

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [∀ U : RingedSite.ofCommRingSheaf JY OY,
  HasWeakSheafify
    ((RingedSite.ofCommRingSheaf JY OY).localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf JY OY,
  ((RingedSite.ofCommRingSheaf JY OY).localization U).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [KFlat.HomotopyTensorDescends (J := JX) OX]
variable [KFlat.TensorDescends (J := JX) OX]
variable [KFlat.IsLocalization (J := JX) OX]
variable [KFlat.HomotopyTensorDescends (J := JY) OY]
variable [KFlat.TensorDescends (J := JY) OY]
variable [KFlat.IsLocalization (J := JY) OY]

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.modulePushforward.{w}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{w} f)
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf JX OX))]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{w} f)
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
variable [DerivedAdjunction.HasPair.{w} f]
variable [Functor.Monoidal (modulePullbackDerived.{w} f)]

/-- Stacks 0944: the right-oriented projection-formula mate for derived pullback is an isomorphism
when its source-side tensor factor is perfect. -/
@[stacks 0944 "right tensor orientation"]
theorem IsPerfect.isIso_projectionFormulaMate
    {K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)}
    (hK : IsPerfect K)
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX)) :
    IsIso ((moduleDerivedAdjunction f).projectionFormulaMate K E) := sorry

/-- Stacks 0944: the left-oriented projection-formula mate for derived pullback is an isomorphism
when its target-side tensor factor is perfect. -/
@[stacks 0944 "left tensor orientation"]
theorem IsPerfect.isIso_leftProjectionFormulaMate
    {K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JY OY)}
    (hK : IsPerfect K)
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf JX OX)) :
    IsIso ((moduleDerivedAdjunction f).leftProjectionFormulaMate E K) := sorry

end RingedSite.Hom.ModuleDerived
