/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Separation

@[expose] public section

universe u

/- Lemma 39.7.3: The underlying scheme of a group scheme over a field is separated. -/
@[stacks 047L] #check (AlgebraicGeometry.GroupScheme.instIsSeparated :
  ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
    [CategoryTheory.GrpObj G], G.left.IsSeparated)
