/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionChange

@[expose] public section

open scoped BigOperators

/- 55.11.9.3: if `components` is the component support of `D'`, excludes `i`, and at least one
of its components meets `C_i`, then the sum of `a_ij - 1` over the components
meeting `C_i`, less `w_i - 1`, is nonnegative. -/
@[stacks 0CED]
#check (NumericalType.changeIntersections_nonnegative :
  ∀ (T : NumericalType) (i : Fin T.n) (components : Finset (Fin T.n)),
    i ∉ components → (∃ j ∈ components, 0 < T.intersection i j) →
    0 ≤ (∑ j ∈ components with 0 < T.intersection i j,
      T.intersection i j - 1) - ((T.weight i : ℤ) - 1))
