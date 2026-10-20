/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.«91_7_0_1_Solution»
public import stacks_project.Chap91.Remark_91_4_5_Equivalence

/-!
# Split square-zero solution of the identity ringed-space diagram

The identity diagram 0 ⟶ 0 ⟶ 𝒪_S ⟶ 𝒪_S ⟶ 0 with zero kernel map 0 ⟶ 𝒢 admits
the split solution whose middle ringed space is `ofModuleSpace G`, i.e. the
source's 𝒢 ⊕ 𝒪_X.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening hiding Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

/-- The unique map `Ker(id : S ⟶ S) ⟶ f_* 𝒢` in the identity diagram. -/
def zeroKernelMap {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules) :
    Hom.idealModule (𝟙 S) ⟶ (f _*).obj G :=
  0

/-- `zeroKernelMap` is the zero morphism of 𝒪_S-modules. -/
theorem zeroKernelMap_eq_zero {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules) :
    zeroKernelMap f G = 0 := sorry

/-- `zeroKernelMap` sends every kernel section to zero. -/
theorem zeroKernelMap_apply {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules)
    {U : (TopologicalSpace.Opens S)ᵒᵖ} (x : (Hom.idealModule (𝟙 S)).val.obj U) :
    (zeroKernelMap f G).val.app U x = 0 := sorry

/-- Identification of `Ker((inclusion G)^♯)` with 𝒢, via `snd` and `inr` of
`ofModuleSpace G`. -/
def kernelIso_inclusion {X : RingedSpace.{u}} (G : X.Modules) :
    Hom.idealModule (inclusion G) ≅ G :=
  ofModule_idealIso G

/-- The forward kernel identification is the adjunct of `ofModule_kernelToPushforward`. -/
theorem kernelIso_inclusion_hom {X : RingedSpace.{u}} (G : X.Modules) :
    (kernelIso_inclusion G).hom =
      ((inclusion G) ^*).map (ofModule_kernelToPushforward G) ≫
        (pullbackPushforwardAdjunction (inclusion G)).counit.app G := sorry

/-- The inverse kernel identification is the adjunct of `ofModule_pushforwardToKernel`. -/
theorem kernelIso_inclusion_inv {X : RingedSpace.{u}} (G : X.Modules) :
    (kernelIso_inclusion G).inv =
      (asIso ((pullbackPushforwardAdjunction (inclusion G)).counit.app G)).inv ≫
        ((inclusion G) ^*).map (ofModule_pushforwardToKernel G) := sorry

/-- The split solution of the identity diagram, with middle space `ofModuleSpace G`. -/
def trivialSolution {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules) :
    Solution (𝟙 S) f G (zeroKernelMap f G) :=
  Solution.of (𝟙 S) f G (zeroKernelMap f G) (inclusion G) (retraction G ≫ f) sorry
    (kernelIso_inclusion G) sorry

/-- The carrier of the split solution is `ofModuleSpace G`. -/
theorem trivialSolution_space {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules) :
    (trivialSolution f G).space = ofModuleSpace G := sorry

/-- The thickening of the split solution is `inclusion G`. -/
theorem trivialSolution_i {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules) :
    (trivialSolution f G).i = inclusion G := sorry

/-- The structure map of the split solution is `retraction G ≫ f`. -/
theorem trivialSolution_f' {S X : RingedSpace.{u}} (f : X ⟶ S) (G : X.Modules) :
    (trivialSolution f G).f' = retraction G ≫ f := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
