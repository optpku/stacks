/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.TopologicalGenus

/- Definition 55.3.11: the topological genus of a numerical type `T` is the
nonnegative integer represented by `1 - T.n + T.edgeCount`. -/
@[stacks 0C79] #check (NumericalType.topologicalGenus : NumericalType → ℕ)
