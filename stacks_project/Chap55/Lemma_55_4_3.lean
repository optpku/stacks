/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionCokernel

/- Lemma 55.4.3 -/
@[stacks 0CE7] #check (NumericalType.picardToIntersectionCokernel_injective :
  ∀ (T : NumericalType), Function.Injective T.picardToIntersectionCokernel)
