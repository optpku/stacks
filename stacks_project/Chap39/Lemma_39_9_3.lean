/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.BaseChange

@[expose] public section

universe u

open AlgebraicGeometry
open AlgebraicGeometry.FieldExtension.Over

/- Lemma 39.9.3: base change along a field extension preserves abelian varieties. -/
@[stacks 0BFB] #check
  (AlgebraicGeometry.FieldExtension.Over.instAbelianVariety :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (A : SchemeOverField k) [CategoryTheory.GrpObj A]
      [AbelianVariety A],
      AbelianVariety (baseChange k K A))
