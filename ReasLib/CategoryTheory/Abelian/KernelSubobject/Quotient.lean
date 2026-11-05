/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-! # The cokernel of the kernel subobject of an epimorphism

The universal witnesses below are the native kernel and cokernel witnesses. No inverse is
extracted from a separate invertibility assertion.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : C} (f : X ⟶ Y) [Epi f]

/-- An epimorphism is the cokernel of its actual kernel. -/
def kernelCokernelIsoOfEpi : cokernel (kernel.ι f) ≅ Y := by
  let h := epiIsCokernelOfKernel
    (KernelFork.ofι (kernel.ι f) (kernel.condition f)) (kernelIsKernel f)
  exact (cokernelIsCokernel (kernel.ι f)).coconePointUniqueUpToIso h

/-- The cokernel of the canonical kernel-subobject arrow is the specified epimorphism's target. -/
def kernelSubobjectCokernelIso : cokernel (kernelSubobject f).arrow ≅ Y :=
  cokernelIsoOfEq (kernelSubobject_arrow f).symm ≪≫
    cokernelEpiComp (kernelSubobjectIso f).hom (kernel.ι f) ≪≫
    kernelCokernelIsoOfEpi f

/-- The cokernel comparison identifies the projection with the specified epimorphism. -/
@[reassoc (attr := simp)]
theorem π_comp_kernelSubobjectCokernelIso_hom :
    cokernel.π (kernelSubobject f).arrow ≫ (kernelSubobjectCokernelIso f).hom = f := by
  simp [kernelSubobjectCokernelIso, kernelCokernelIsoOfEpi,
    IsColimit.coconePointUniqueUpToIso]
  exact (cokernelIsCokernel (kernel.ι f)).fac
    (CokernelCofork.ofπ f (kernel.condition f)) WalkingParallelPair.one

end CategoryTheory.Abelian
