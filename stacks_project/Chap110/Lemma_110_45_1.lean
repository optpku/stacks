/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Idempotents
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 110.45.1 -/
@[stacks 04QL]
#check (AlgebraicGeometry.exists_affine_closedSubscheme_locally_cutOutByIdempotents_not_globally :
    ∃ (A : CommRingCat.{u}) (T : (Spec A).IdealSheafData),
      T.IsLocallyCutOutByIdempotents ∧ ¬ T.IsCutOutByIdempotents)
