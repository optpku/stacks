/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Graph

@[expose] public section

namespace NumericalType

/-- The topological genus of a numerical type. -/
public def topologicalGenus (T : NumericalType) : ℕ :=
  T.edgeCount + 1 - T.n

/-- The topological genus is computed from the number of positive-intersection edges
and the number of indices. -/
public theorem topologicalGenus_eq (T : NumericalType) :
    T.topologicalGenus = T.edgeCount + 1 - T.n := sorry

/-- The topological genus, cast to `ℤ`, is the nonnegative integer
`1 - T.n + T.edgeCount`. -/
public theorem topologicalGenus_cast (T : NumericalType) :
    (T.topologicalGenus : ℤ) = 1 - (T.n : ℤ) + (T.edgeCount : ℤ) := sorry

end NumericalType
