/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.Nonexistence

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 110.28.1: there exists a quasi-compact and quasi-separated algebraic
space which does not contain a quasi-compact dense open subscheme. -/
@[stacks 087I] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_no_quasiCompact_dense_open :
    ∃ (k : Type u) (_ : Field k) (X : AlgebraicSpace (Spec (CommRingCat.of k))),
      AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact X ∧
        AlgebraicGeometry.AlgebraicSpace.IsQuasiSeparated X ∧
        ¬ AlgebraicGeometry.AlgebraicSpace.HasQuasiCompactDenseOpenSubscheme X)
