/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Reduced

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Remark 39.8.3: every group scheme over a characteristic-zero field has reduced underlying
scheme, without a local finite-type hypothesis. -/
@[stacks 047O] #check
  (AlgebraicGeometry.GroupScheme.instIsReducedOfCharZero :
    ∀ {k : Type u} [Field k] [CharZero k] (G : SchemeOverField k) [GrpObj G],
      IsReduced G.left)
