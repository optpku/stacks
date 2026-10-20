/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.IdealMultiple
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.FlatMorphismSquare

/-!
# Canonical comparison maps for a strict first-order thickening square

For a commutative square of first-order thickenings of ring sheaves, the comparison
`f^* J ⊗_O F ⟶ I ⊗_O F ⟶ I F'` is the tensor of `kernelPullbackMap` followed by
`infMap` of the mixed-scalar extension `ofPullback π F'`.
-/

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
variable {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O)
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]

/-- Along a first-order thickening, the extension-restriction unit is invertible on
`idealMulO' π F'`. -/
instance instIsIso_extendRestrictUnit_idealMulO' [IsFirstOrderThickening π]
    {F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O'} :
    IsIso (extendRestrictUnit π (idealMulO' π F')) := sorry

/-- The mixed-scalar extension `0 ⟶ I F' ⟶ F' ⟶ i^* F' ⟶ 0` associated to an `O'`-module
`F'` on the first-order thickening `π`. -/
def ofPullback [IsFirstOrderThickening π] (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    Extension π where
  kernel := idealMul π F'
  middle := F'
  quot := (extendScalars (ringSheafMap π)).obj F'
  ι := (asIso (extendRestrictUnit π (idealMulO' π F'))).inv ≫
    kernel.ι (extendRestrictUnit π F')
  p := extendRestrictUnit π F'
  zero := by
    dsimp only [idealMul, idealMulO']
    rw [Category.assoc, kernel.condition, comp_zero]
    rfl
  shortExact := sorry

variable [hπ : IsFirstOrderThickening π]

/-- The kernel of `ofPullback π F'` is the `O`-module `I F'`. -/
theorem ofPullback_kernel
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    (ofPullback π F').kernel = idealMul π F' := rfl

/-- The middle term of `ofPullback π F'` is `F'`. -/
theorem ofPullback_middle
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    (ofPullback π F').middle = F' := rfl

/-- The quotient of `ofPullback π F'` is `i^* F'`. -/
theorem ofPullback_quot
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    (ofPullback π F').quot = (extendScalars (ringSheafMap π)).obj F' := rfl

/-- The comparison `I ⊗_O F ⟶ I F'` obtained as `infMap` of `ofPullback π F'`. -/
def idealMulInfMap (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    moduleTensor (ideal π) ((extendScalars (ringSheafMap π)).obj F') ⟶
      idealMul π F' :=
  infMap hπ.isSquareZero (ofPullback π F')

/-- `idealMulInfMap` is `infMap` of `ofPullback π F'`. -/
theorem idealMulInfMap_eq
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    idealMulInfMap π F' = infMap hπ.isSquareZero (ofPullback π F') := rfl

variable {OB' OB : Sheaf J CommRingCat.{max u v}} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening τ]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)

/-- The comparison `f^* J ⊗_O F ⟶ I ⊗_O F` induced by `kernelPullbackMap`. -/
def sourceIdealTensorMap
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj F') ⟶
      moduleTensor (ideal π) ((extendScalars (ringSheafMap π)).obj F') :=
  moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 _)

/-- `sourceIdealTensorMap` is the tensor morphism of `kernelPullbackMap` with `𝟙 F`. -/
theorem sourceIdealTensorMap_eq
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    sourceIdealTensorMap π f f' hcomm F' =
      moduleTensorMap (kernelPullbackMap f f' hcomm) (𝟙 _) := rfl

/-- The canonical comparison from the pulled-back base ideal tensored with the reduced
module to the ideal multiple of the original module. -/
def canonicalMap (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
        ((extendScalars (ringSheafMap π)).obj F') ⟶
      idealMul π F' :=
  sourceIdealTensorMap π f f' hcomm F' ≫ idealMulInfMap π F'

/-- `canonicalMap` is the composite `sourceIdealTensorMap ≫ idealMulInfMap`. -/
theorem canonicalMap_eq
    (F' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O') :
    canonicalMap π f f' hcomm F' =
      sourceIdealTensorMap π f f' hcomm F' ≫ idealMulInfMap π F' := rfl

end SheafOfModules.RingedSite.FirstOrderThickening
