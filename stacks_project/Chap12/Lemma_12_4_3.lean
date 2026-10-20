/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Idempotents.Countable
import StacksCheckRecall

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Lemma 12.4.3 (1) [05QV]: countable products and kernels of split epimorphisms imply
idempotent completeness. -/
@[stacks 05QV]
#check (CategoryTheory.Idempotents.isIdempotentComplete_of_countableProducts_of_splitEpiKernels :
  [HasCountableProducts C] →
    (∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsSplitEpi f], HasKernel f) →
      IsIdempotentComplete C)

/- Lemma 12.4.3 (2) [05QV]: dually, countable coproducts and cokernels of split monomorphisms
imply idempotent completeness. -/
@[stacks 05QV]
#check (CategoryTheory.Idempotents.isIdempotentComplete_of_countableCoproducts_of_splitMonoCokernels :
  [HasCountableCoproducts C] →
    (∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsSplitMono f], HasCokernel f) →
      IsIdempotentComplete C)
