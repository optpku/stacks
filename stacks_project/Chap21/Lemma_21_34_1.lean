/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.34.1

The tensor/internal-Hom isomorphism is the generic braided closed-monoidal owner.  The ringed-site
module-complex presentation is a specialization and does not need a second declaration here.
-/

/- Lemma 21.34.1 (0A90): canonical tensor/internal-Hom isomorphism. -/
@[stacks 0A90 "tensor/internal-Hom isomorphism"] #check
  @CategoryTheory.MonoidalClosed.internalHomTensorIso

/- The three variance components record the source functoriality. -/
@[stacks 0A90 "tensor/internal-Hom naturality in the left variable"] #check
  @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_left
@[stacks 0A90 "tensor/internal-Hom naturality in the middle variable"] #check
  @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_middle
@[stacks 0A90 "tensor/internal-Hom naturality in the right variable"] #check
  @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_right
