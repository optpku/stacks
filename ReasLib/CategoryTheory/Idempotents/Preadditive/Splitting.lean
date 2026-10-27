/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Idempotents.Preadditive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Idempotents

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- An idempotent and its complement annihilate one another. -/
theorem comp_complement {X : C} (f : X ⟶ X) (hf : f ≫ f = f) :
    f ≫ (𝟙 X - f) = 0 ∧ (𝟙 X - f) ≫ f = 0 := by
  constructor <;> simp [Preadditive.comp_sub, Preadditive.sub_comp, hf]

/-- Factoring the complementary projector through the kernel gives a retraction
which is also a cokernel. No other kernels or cokernels are assumed. -/
theorem kernel_retraction_is_cokernel {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasKernel f] (p : X ⟶ kernel f) (hp : p ≫ kernel.ι f = 𝟙 X - f) :
    kernel.ι f ≫ p = 𝟙 (kernel f) ∧
      ∃ h : f ≫ p = 0, Nonempty (IsColimit (CokernelCofork.ofπ p h)) := sorry

/-- Dually, factoring the complement through a cokernel gives a section which
is also a kernel. -/
theorem cokernel_section_is_kernel {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasCokernel f] (i : cokernel f ⟶ X) (hi : cokernel.π f ≫ i = 𝟙 X - f) :
    i ≫ cokernel.π f = 𝟙 (cokernel f) ∧
      ∃ h : i ≫ f = 0, Nonempty (IsLimit (KernelFork.ofι i h)) := sorry

/-- Factoring an idempotent through the kernel of its complement gives a retraction
which is also a cokernel of the complement. -/
theorem kernelComplementSplitting {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasKernel (𝟙 X - f)] (q : X ⟶ kernel (𝟙 X - f))
    (hq : q ≫ kernel.ι (𝟙 X - f) = f) :
    kernel.ι (𝟙 X - f) ≫ q = 𝟙 (kernel (𝟙 X - f)) ∧
      ∃ h : (𝟙 X - f) ≫ q = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ q h)) := sorry

/-- Factoring an idempotent through the cokernel of its complement gives a section
which is also a kernel of the complement. -/
theorem cokernelComplementSplitting {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
    [HasCokernel (𝟙 X - f)] (j : cokernel (𝟙 X - f) ⟶ X)
    (hj : cokernel.π (𝟙 X - f) ≫ j = f) :
    j ≫ cokernel.π (𝟙 X - f) = 𝟙 (cokernel (𝟙 X - f)) ∧
      ∃ h : j ≫ (𝟙 X - f) = 0,
        Nonempty (IsLimit (KernelFork.ofι j h)) := sorry

/-- If each complementary idempotent has a kernel or a cokernel, both split.
The same first summand is a kernel and a cokernel of `f`, and the same second
summand is a kernel and a cokernel of its complement. Thus this single
biproduct realizes all four kernel/cokernel combinations. -/
theorem exists_biproduct_of_kernel_or_cokernel {X : C} (f : X ⟶ X)
    (hf : f ≫ f = f) (h₁ : HasKernel f ∨ HasCokernel f)
    (h₂ : HasKernel (𝟙 X - f) ∨ HasCokernel (𝟙 X - f)) :
    ∃ (K L : C) (_ : HasBinaryBiproduct K L) (e : X ≅ K ⊞ L)
      (i : K ⟶ X) (p : X ⟶ K) (j : L ⟶ X) (q : X ⟶ L),
      i = biprod.inl ≫ e.inv ∧ p = e.hom ≫ biprod.fst ∧
      j = biprod.inr ≫ e.inv ∧ q = e.hom ≫ biprod.snd ∧
      i ≫ p = 𝟙 K ∧ j ≫ q = 𝟙 L ∧ p ≫ i = 𝟙 X - f ∧ q ≫ j = f ∧
      ∃ (hi : i ≫ f = 0) (hp : f ≫ p = 0)
        (hj : j ≫ (𝟙 X - f) = 0) (hq : (𝟙 X - f) ≫ q = 0),
        Nonempty (IsLimit (KernelFork.ofι i hi)) ∧
        Nonempty (IsColimit (CokernelCofork.ofπ p hp)) ∧
        Nonempty (IsLimit (KernelFork.ofι j hj)) ∧
        Nonempty (IsColimit (CokernelCofork.ofπ q hq)) := sorry

/-- A section and retraction are respectively a kernel and a cokernel of the
complementary projector, in an arbitrary preadditive category. -/
theorem split_morphism_kernel_cokernel {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y)
    (hj : j ≫ q = 𝟙 Y) :
    ∃ (hi : j ≫ (𝟙 X - q ≫ j) = 0) (hp : (𝟙 X - q ≫ j) ≫ q = 0),
      Nonempty (IsLimit (KernelFork.ofι j hi)) ∧
      Nonempty (IsColimit (CokernelCofork.ofπ q hp)) := sorry

/-- A split pair extends to a biproduct as soon as its projector has a kernel
or a cokernel. The complementary summand is simultaneously both, and the
biproduct maps on the given summand are the original section and retraction. -/
theorem split_morphism_biproduct {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y)
    (hj : j ≫ q = 𝟙 Y) (h : HasKernel (q ≫ j) ∨ HasCokernel (q ≫ j)) :
    ∃ (K : C) (_ : HasBinaryBiproduct K Y) (e : X ≅ K ⊞ Y)
      (i : K ⟶ X) (p : X ⟶ K),
      i = biprod.inl ≫ e.inv ∧ p = e.hom ≫ biprod.fst ∧
      j = biprod.inr ≫ e.inv ∧ q = e.hom ≫ biprod.snd ∧
      i ≫ p = 𝟙 K ∧ p ≫ i = 𝟙 X - q ≫ j ∧
      ∃ (hi : i ≫ (q ≫ j) = 0) (hp : (q ≫ j) ≫ p = 0),
        Nonempty (IsLimit (KernelFork.ofι i hi)) ∧
        Nonempty (IsColimit (CokernelCofork.ofπ p hp)) := sorry

end CategoryTheory.Idempotents
