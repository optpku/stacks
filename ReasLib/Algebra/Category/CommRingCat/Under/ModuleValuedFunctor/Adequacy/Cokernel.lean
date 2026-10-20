/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Cokernel
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Generators
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.FiniteFreeExtension

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor.TensorAdequate

/-- Tensor adequacy is preserved by the pointwise cokernel of a morphism into a
tensor-extension functor. -/
theorem cokernelToTensorExtension {A : CommRingCat.{u}}
    {F : ModuleValuedFunctor.bundled.{u, u} A} {M : ModuleCat.{u} A}
    (φ : F ⟶ (ModuleValuedFunctor.tensorExtensionFunctor A).obj M)
    (hF : ModuleValuedFunctor.TensorAdequate F) :
    ModuleValuedFunctor.TensorAdequate (ModuleValuedFunctor.pointwiseCokernel φ) := sorry

end ModuleValuedFunctor.TensorAdequate

namespace ModuleValuedFunctor.Adequate

/-- Tensor adequacy is preserved by the pointwise cokernel of any morphism between
tensor-adequate module-valued functors. -/
theorem cokernel {A : CommRingCat.{u}}
    {F G : ModuleValuedFunctor.bundled.{u, u} A} (φ : F ⟶ G)
    (hF : ModuleValuedFunctor.TensorAdequate F)
    (hG : ModuleValuedFunctor.TensorAdequate G) :
    ModuleValuedFunctor.TensorAdequate (ModuleValuedFunctor.pointwiseCokernel φ) := sorry

end ModuleValuedFunctor.Adequate
