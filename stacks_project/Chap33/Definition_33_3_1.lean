/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety

@[expose] public section

/-!
# Definition 33.3.1 compatibility entry point

The reusable variety typeclass is owned by
`ReasLib.AlgebraicGeometry.Scheme.Variety`.
-/

universe u

/- Definition 33.3.1 states that a variety over a field is an integral scheme whose structure
morphism is separated and of finite type. -/
@[stacks 020D] #check
  (AlgebraicGeometry.variety_iff :
    ∀ {k : Type u} [Field k]
      (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))),
      AlgebraicGeometry.Variety X ↔
        AlgebraicGeometry.IsIntegral X.left ∧ AlgebraicGeometry.IsSeparated X.hom ∧
          AlgebraicGeometry.Scheme.Hom.FiniteType X.hom)
