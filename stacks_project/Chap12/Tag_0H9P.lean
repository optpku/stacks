/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Idempotents.Preadditive.Splitting
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X : C}

/- Lemma (0H9P) (1): the factorization of the complement through the kernel
is a retraction and a cokernel of f. -/
@[stacks 0H9P] #check (CategoryTheory.Idempotents.kernel_retraction_is_cokernel :
  ∀ (f : X ⟶ X) (hf : f ≫ f = f) [HasKernel f]
    (p : X ⟶ kernel f) (hp : p ≫ kernel.ι f = 𝟙 X - f),
    kernel.ι f ≫ p = 𝟙 (kernel f) ∧
      ∃ h : f ≫ p = 0, Nonempty (IsColimit (CokernelCofork.ofπ p h)))

/- Lemma (0H9P) (2): the factorization of the complement through the cokernel
is a section and a kernel of f. -/
@[stacks 0H9P] #check (CategoryTheory.Idempotents.cokernel_section_is_kernel :
  ∀ (f : X ⟶ X) (hf : f ≫ f = f) [HasCokernel f]
    (i : cokernel f ⟶ X) (hi : cokernel.π f ≫ i = 𝟙 X - f),
    i ≫ cokernel.π f = 𝟙 (cokernel f) ∧
      ∃ h : i ≫ f = 0, Nonempty (IsLimit (KernelFork.ofι i h)))

/- Lemma (0H9P) (3): factoring f through the kernel of 𝟙 X - f gives a
retraction which is also a cokernel of 𝟙 X - f. -/
@[stacks 0H9P] #check (CategoryTheory.Idempotents.kernelComplementSplitting :
  ∀ (f : X ⟶ X) (hf : f ≫ f = f) [HasKernel (𝟙 X - f)]
    (q : X ⟶ kernel (𝟙 X - f)) (hq : q ≫ kernel.ι (𝟙 X - f) = f),
    kernel.ι (𝟙 X - f) ≫ q = 𝟙 (kernel (𝟙 X - f)) ∧
      ∃ h : (𝟙 X - f) ≫ q = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ q h)))

/- Lemma (0H9P) (4): factoring f through the cokernel of 𝟙 X - f gives a
section which is also a kernel of 𝟙 X - f. -/
@[stacks 0H9P] #check (CategoryTheory.Idempotents.cokernelComplementSplitting :
  ∀ (f : X ⟶ X) (hf : f ≫ f = f) [HasCokernel (𝟙 X - f)]
    (j : cokernel (𝟙 X - f) ⟶ X) (hj : cokernel.π (𝟙 X - f) ≫ j = f),
    j ≫ cokernel.π (𝟙 X - f) = 𝟙 (cokernel (𝟙 X - f)) ∧
      ∃ h : j ≫ (𝟙 X - f) = 0,
        Nonempty (IsLimit (KernelFork.ofι j h)))
