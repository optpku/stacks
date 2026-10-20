/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coimage-Image Factorizations

The canonical comparison from coimage to image and its source-facing universal property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : C} (f : X ⟶ Y)
variable [HasKernel f] [HasCokernel f] [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)]

/-- Lemma 12.3.12: the coimage-image comparison is the unique morphism whose composite with
the canonical epimorphism and monomorphism recovers `f`. -/
@[stacks 0107]
theorem coimageImageComparison_unique :
    ∃! g : CategoryTheory.Abelian.coimage f ⟶ CategoryTheory.Abelian.image f,
      CategoryTheory.Abelian.coimage.π f ≫ g ≫ CategoryTheory.Abelian.image.ι f = f := sorry

end CategoryTheory.Abelian
