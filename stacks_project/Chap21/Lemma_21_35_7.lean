/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.35.7

The tensor/internal-Hom comparison in the derived category is a specialization of the generic
braided closed-monoidal owner.  Its uncurrying formula and all three variance directions are
already part of the reusable ReasLib API, so this chapter item does not duplicate a
ringed-site-specific construction.
-/

/- Lemma 21.35.7 (0BYU): the canonical map
`K ⊗ RHom(M, L) ⟶ RHom(M, K ⊗ L)`. -/
@[stacks 0BYU "tensor/internal-Hom comparison"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison

@[stacks 0BYU "tensor/internal-Hom evaluation specification"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_uncurry

@[stacks 0BYU "tensor/internal-Hom tensor naturality"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_tensor

@[stacks 0BYU "tensor/internal-Hom target naturality"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_target

@[stacks 0BYU "tensor/internal-Hom source naturality"] #check
  @CategoryTheory.MonoidalClosed.tensorInternalHomComparison_natural_source
