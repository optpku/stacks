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

/- Lemma (0H9S). In a preadditive category, a split pair `j ≫ q = 𝟙 Y`
extends to `X ≅ K ⊞ Y` if `q ≫ j` has a kernel or a cokernel. The summand
`K` is simultaneously a kernel and a cokernel, and the biproduct maps on `Y`
are the prescribed `j` and `q`. Universal-property comparison identifies `K`
with either chosen (co)kernel and preserves its canonical morphism. The
remaining map is uniquely determined by `p ≫ i = 𝟙 X - q ≫ j`, using
monicity of the kernel inclusion or epicity of the cokernel projection. -/
@[stacks 0H9S] #check (CategoryTheory.Idempotents.split_morphism_biproduct :
  ∀ {X Y : C} (j : Y ⟶ X) (q : X ⟶ Y)
    (hj : j ≫ q = 𝟙 Y) (h : HasKernel (q ≫ j) ∨ HasCokernel (q ≫ j)),
    ∃ (K : C) (_ : HasBinaryBiproduct K Y) (e : X ≅ K ⊞ Y)
      (i : K ⟶ X) (p : X ⟶ K),
      i = biprod.inl ≫ e.inv ∧ p = e.hom ≫ biprod.fst ∧
      j = biprod.inr ≫ e.inv ∧ q = e.hom ≫ biprod.snd ∧
      i ≫ p = 𝟙 K ∧ p ≫ i = 𝟙 X - q ≫ j ∧
      ∃ (hi : i ≫ (q ≫ j) = 0) (hp : (q ≫ j) ≫ p = 0),
        Nonempty (IsLimit (KernelFork.ofι i hi)) ∧
        Nonempty (IsColimit (CokernelCofork.ofπ p hp)))
