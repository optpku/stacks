/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType

@[expose] public section

open scoped BigOperators

namespace NumericalType

/-- For a finite set of indices excluding a distinguished index and containing
an index with positive intersection with it, the sum of the positive intersection
entries minus one is at least the distinguished weight minus one. -/
public theorem changeIntersections_nonnegative (T : NumericalType) (i : Fin T.n)
    (components : Finset (Fin T.n)) (h_i : i ∉ components)
    (hmeet : ∃ j ∈ components, 0 < T.intersection i j) :
    0 ≤ (∑ j ∈ components with 0 < T.intersection i j,
      T.intersection i j - 1) - ((T.weight i : ℤ) - 1) := sorry

end NumericalType
