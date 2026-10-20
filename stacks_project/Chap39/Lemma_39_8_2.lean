/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Smooth

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 39.8.2: a locally algebraic group scheme over a characteristic-zero field has smooth
structure morphism. -/
@[stacks 047N] #check
  (AlgebraicGeometry.GroupScheme.instSmoothOfCharZero :
    ∀ {k : Type u} [Field k] [CharZero k] (G : SchemeOverField k) [GrpObj G]
      [LocallyAlgebraic G], Smooth G.hom)
