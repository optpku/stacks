/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ScalarDescent
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening

/-!
# The module `ℐℱ'` along a morphism of ringed spaces

The `𝒪_{X'}`-module `ℐℱ'` is the kernel of the pullback-pushforward unit
`ℱ' ⟶ i_* i^* ℱ'`. Along a first-order thickening this kernel carries a unique
`𝒪_X`-module structure, recovered by inverse image, and the canonical sequence
`0 ⟶ ℐℱ' ⟶ ℱ' ⟶ i_* i^* ℱ'` is a mixed-scalar extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite.IdealSheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X X' : RingedSpace.{u}} (i : X ⟶ X')

/-- The `𝒪_{X'}`-module `ℐℱ'`, as the kernel of the pullback-pushforward unit of `ℱ'`. -/
def idealMul (F' : X'.Modules) : X'.Modules :=
  kernel ((pullbackPushforwardAdjunction i).unit.app F')

/-- `idealMul i F'` is the kernel of `ℱ' ⟶ i_* i^* ℱ'`. -/
theorem idealMul_eq (F' : X'.Modules) :
    idealMul i F' = kernel ((pullbackPushforwardAdjunction i).unit.app F') := sorry

/-- The inverse image of the reduction kernel as an `𝒪_X`-module. -/
def idealMulRestrict (F' : X'.Modules) : X.Modules :=
  (i^*).obj (idealMul i F')

/-- `idealMulRestrict i F'` is `i^*` of `idealMul i F'`. -/
theorem idealMulRestrict_eq (F' : X'.Modules) :
    idealMulRestrict i F' = (i^*).obj (idealMul i F') := sorry

/-- The canonical inclusion `ℐℱ' ⟶ ℱ'` of `𝒪_{X'}`-modules. -/
def idealMulι (F' : X'.Modules) : idealMul i F' ⟶ F' :=
  kernel.ι ((pullbackPushforwardAdjunction i).unit.app F')

/-- The inclusion of `ℐℱ'` composes to zero with the pullback-pushforward unit of `ℱ'`. -/
theorem idealMul_comp_unit (F' : X'.Modules) :
    idealMulι i F' ≫ (pullbackPushforwardAdjunction i).unit.app F' = 0 := sorry

/-- Along a first-order thickening, the pullback-pushforward unit of `ℱ'` is an epimorphism. -/
theorem instEpi_unit_app [IsFirstOrderThickening i] {F' : X'.Modules} :
    Epi ((pullbackPushforwardAdjunction i).unit.app F') := sorry

/-- The kernel-ideal action on `ℱ'` factors through the pullback-pushforward unit. -/
theorem action_comp_unit [IsFirstOrderThickening i] (F' : X'.Modules) :
    action (kernelIdealSubobject i) F' ≫
      (pullbackPushforwardAdjunction i).unit.app F' = 0 := sorry

/-- The kernel-ideal action `ℐ ⊗ ℱ' ⟶ ℱ'` factors through `ℐℱ'`. -/
def actionToIdealMul [IsFirstOrderThickening i] (F' : X'.Modules) :
    kernelIdealSheaf i ⊗ F' ⟶ idealMul i F' :=
  kernel.lift ((pullbackPushforwardAdjunction i).unit.app F')
    (action (kernelIdealSubobject i) F') (action_comp_unit i F')

/-- Factoring the kernel-ideal action through `ℐℱ'` recovers the action into `ℱ'`. -/
theorem actionToIdealMul_comp_ι [IsFirstOrderThickening i] (F' : X'.Modules) :
    actionToIdealMul i F' ≫ idealMulι i F' = action (kernelIdealSubobject i) F' := sorry

/-- The image inclusion of the kernel-ideal action is killed by the unit of `ℱ'`. -/
theorem action_image_ι_comp_unit [IsFirstOrderThickening i] (F' : X'.Modules) :
    image.ι (action (kernelIdealSubobject i) F') ≫
      (pullbackPushforwardAdjunction i).unit.app F' = 0 := sorry

/-- The comparison from the image of the kernel-ideal action to `ℐℱ'`. -/
def imageToIdealMul [IsFirstOrderThickening i] (F' : X'.Modules) :
    image (action (kernelIdealSubobject i) F') ⟶ idealMul i F' :=
  kernel.lift ((pullbackPushforwardAdjunction i).unit.app F')
    (image.ι (action (kernelIdealSubobject i) F')) (action_image_ι_comp_unit i F')

/-- Along a first-order thickening, the image of `ℐ ⊗ ℱ' ⟶ ℱ'` is `ℐℱ'`. -/
instance instIsIso_imageToIdealMul [IsFirstOrderThickening i] {F' : X'.Modules} :
    IsIso (imageToIdealMul i F') := sorry

/-- The reduction kernel is annihilated by the kernel of the structure-sheaf map along a
first-order thickening. -/
theorem idealMul_annihilated [IsFirstOrderThickening i] (F' : X'.Modules) :
    SheafOfModules.IsAnnihilatedByKernel (toRingCatSheafHom i) (idealMul i F') := sorry

/-- The explicit inverse to reduction on ideal multiples is obtained by scalar descent. -/
def idealMulUnitInv [IsFirstOrderThickening i] (F' : X'.Modules) :
    (i _*).obj (idealMulRestrict i F') ⟶ idealMul i F' :=
  ScalarDescent.unitInv i (idealMul i F') (idealMul_annihilated i F')

/-- Reduction followed by its supplied inverse is the identity on ideal multiples. -/
theorem unit_comp_idealMulUnitInv [IsFirstOrderThickening i] (F' : X'.Modules) :
    (pullbackPushforwardAdjunction i).unit.app (idealMul i F') ≫ idealMulUnitInv i F' =
      𝟙 (idealMul i F') :=
  ScalarDescent.unit_comp_unitInv i (idealMul i F') (idealMul_annihilated i F')

/-- The supplied inverse followed by reduction is the identity on pushed-forward reduced
ideal multiples. -/
theorem idealMulUnitInv_comp_unit [IsFirstOrderThickening i] (F' : X'.Modules) :
    idealMulUnitInv i F' ≫ (pullbackPushforwardAdjunction i).unit.app (idealMul i F') =
      𝟙 ((i _*).obj (idealMulRestrict i F')) :=
  ScalarDescent.unitInv_comp_unit i (idealMul i F') (idealMul_annihilated i F')

/-- Along a first-order thickening, reduction is invertible on ideal multiples. -/
instance instIsIso_unit_app_idealMul [IsFirstOrderThickening i] {F' : X'.Modules} :
    IsIso ((pullbackPushforwardAdjunction i).unit.app (idealMul i F')) :=
  ⟨⟨idealMulUnitInv i F', unit_comp_idealMulUnitInv i F',
    idealMulUnitInv_comp_unit i F'⟩⟩

/-- The comparison `Hom_{𝒪_X}(i^* ℱ', ℐ𝒢'_X) ≃ Hom_{𝒪_{X'}}(ℱ', ℐ𝒢')`. -/
def homIdealMulEquiv [IsFirstOrderThickening i] (F' G' : X'.Modules) :
    ((i^*).obj F' ⟶ idealMulRestrict i G') ≃ (F' ⟶ idealMul i G') where
  toFun α :=
    (pullbackPushforwardAdjunction i).homEquiv F' (idealMulRestrict i G') α ≫
      idealMulUnitInv i G'
  invFun β :=
    ((pullbackPushforwardAdjunction i).homEquiv F' (idealMulRestrict i G')).symm
      (β ≫ (pullbackPushforwardAdjunction i).unit.app (idealMul i G'))
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `homIdealMulEquiv` is unit-adjunction followed by the inverse unit on
`ℐ𝒢'`. -/
theorem homIdealMulEquiv_apply [IsFirstOrderThickening i] {F' G' : X'.Modules}
    (α : (i^*).obj F' ⟶ idealMulRestrict i G') :
    homIdealMulEquiv i F' G' α =
      (pullbackPushforwardAdjunction i).homEquiv F' (idealMulRestrict i G') α ≫
        idealMulUnitInv i G' := sorry

namespace ModuleExtension

/-- The canonical mixed-scalar extension `0 ⟶ ℐℱ' ⟶ ℱ' ⟶ i_* i^* ℱ' ⟶ 0`. -/
def ofPullback [IsFirstOrderThickening i] (F' : X'.Modules) : ModuleExtension i :=
  mk (idealMulRestrict i F') ((i^*).obj F') F'
    (idealMulUnitInv i F' ≫
      idealMulι i F')
    ((pullbackPushforwardAdjunction i).unit.app F') sorry sorry

/-- The middle term of `ofPullback i F'` is `ℱ'`. -/
theorem ofPullback_middle [IsFirstOrderThickening i] (F' : X'.Modules) :
    (ofPullback i F').middle = F' := sorry

/-- The kernel of `ofPullback i F'` is `idealMulRestrict i F'`. -/
theorem ofPullback_kernel [IsFirstOrderThickening i] (F' : X'.Modules) :
    (ofPullback i F').kernel = idealMulRestrict i F' := sorry

/-- The cokernel of `ofPullback i F'` is `i^* ℱ'`. -/
theorem ofPullback_cokernel [IsFirstOrderThickening i] (F' : X'.Modules) :
    (ofPullback i F').cokernel = (i^*).obj F' := sorry

/-- The projection of `ofPullback i F'` is the pullback-pushforward unit of `ℱ'`. -/
theorem ofPullback_π [IsFirstOrderThickening i] (F' : X'.Modules) :
    (ofPullback i F').π = (pullbackPushforwardAdjunction i).unit.app F' := sorry

end ModuleExtension

end AlgebraicGeometry.RingedSpace.Hom
