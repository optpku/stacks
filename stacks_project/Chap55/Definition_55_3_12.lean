/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Minimality

/- Definition 55.3.12: A numerical type is minimal when it has no `(-1)`-index. -/
@[stacks 0C7A] #check (NumericalType.IsMinimal : NumericalType → Prop)
