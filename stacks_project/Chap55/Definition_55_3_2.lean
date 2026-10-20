/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Equivalence

/- Definition 55.3.2: two numerical types are equivalent when an equivalence of
their finite index sets preserves multiplicities, intersection-matrix entries,
weights, and component genera pointwise. -/
@[stacks 0C70] #check (NumericalType.Equivalent : NumericalType → NumericalType → Prop)
