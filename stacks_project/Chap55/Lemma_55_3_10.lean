/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Graph

/- Lemma 55.3.10: if `T.edgeCount` counts the pairs `i < j` for which
`0 < T.intersection i j`, then `1 - T.n + T.edgeCount` is nonnegative. -/
@[stacks 0C78] #check
  (NumericalType.topologicalGenusExpression_nonnegative :
    ∀ (T : NumericalType), 0 ≤ (1 : ℤ) - T.n + T.edgeCount)
