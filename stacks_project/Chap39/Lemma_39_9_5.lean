/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety

@[expose] public section

universe u

/- Lemma 39.9.5: the group law of an abelian variety is commutative. -/
@[stacks 0BFD] #check
  (AlgebraicGeometry.AbelianVariety.instIsCommMonObj :
    ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj G] [AlgebraicGeometry.AbelianVariety G],
      CategoryTheory.IsCommMonObj G)
