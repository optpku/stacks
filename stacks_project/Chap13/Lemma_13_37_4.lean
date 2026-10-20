/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Factorization
import StacksCheckRecall

@[expose] public section

-- Lemma 13.37.4: compact maps into a generating-family approximation factor through a finite
-- coproduct-generated triangulated envelope, with an available positive-stage refinement.
@[stacks 09SP] #check @CategoryTheory.IsGeneratingFamilyApproximation.compactFactorization
#check @CategoryTheory.IsGeneratingFamilyApproximation.compactFactorizationAtStage
