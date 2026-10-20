/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Representability

@[expose] public section

/- Lemma 27.13.1: integral projective `n`-space represents equivalence classes of invertible
module sheaves equipped with `n + 1` generating global sections. -/
@[stacks 01NE] #check
  (AlgebraicGeometry.ProjectiveSpaceDatumClass.isRepresentedBy_projectiveSpace :
    ∀ n : ℕ,
      ∃ x : (AlgebraicGeometry.ProjectiveSpaceDatumClass.functor n).obj
          (Opposite.op (AlgebraicGeometry.ProjectiveSpace.scheme ℤ n)),
        (AlgebraicGeometry.ProjectiveSpaceDatumClass.functor n).IsRepresentedBy x)
