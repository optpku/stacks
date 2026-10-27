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

/- Lemma (0H9Q). For an idempotent `f`, if each of `f` and `𝟙 X - f` has
a kernel or a cokernel, then `X ≅ K ⊞ L`, where `K` is both a kernel and a
cokernel of `f`, and `L` is both a kernel and a cokernel of `𝟙 X - f`.
These simultaneous representatives give all four kernel/cokernel presentations.
The biproduct structure maps are `i`, `j`, `p`, `q`, with
`i ≫ p = 𝟙 K`, `j ≫ q = 𝟙 L`, `p ≫ i = 𝟙 X - f`, and `q ≫ j = f`,
as in the preceding kernel/cokernel construction. -/
@[stacks 0H9Q] #check (CategoryTheory.Idempotents.exists_biproduct_of_kernel_or_cokernel :
    ∀ {X : C} (f : X ⟶ X) (hf : f ≫ f = f)
      (h₁ : HasKernel f ∨ HasCokernel f)
      (h₂ : HasKernel (𝟙 X - f) ∨ HasCokernel (𝟙 X - f)),
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
          Nonempty (IsColimit (CokernelCofork.ofπ q hq)))
