/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Genus
public import ReasLib.AlgebraicGeometry.NumericalType.Minimality
public import ReasLib.AlgebraicGeometry.NumericalType.TopologicalGenus

namespace NumericalType

/-- A minimal numerical type with more than one index has genus equal to its
topological genus when all multiplicities and weights are one, all component
genera vanish, and every upper off-diagonal intersection is zero or one. -/
public theorem genus_eq_topologicalGenus (T : NumericalType) (hminimal : T.IsMinimal)
    (hn : 1 < T.n) (hmultiplicity : ∀ i, T.multiplicity i = 1)
    (hweight : ∀ i, T.weight i = 1) (hcomponentGenus : ∀ i, T.componentGenus i = 0)
    (hintersection : ∀ i j, i < j → T.intersection i j ∈ ({0, 1} : Set ℤ)) :
    T.genus = (T.topologicalGenus : ℤ) := sorry

end NumericalType
