module

public import Mathlib.Data.Set.Card
public import ReasLib.AlgebraicGeometry.NumericalType.Genus
public import ReasLib.AlgebraicGeometry.NumericalType.Minimality
public import ReasLib.AlgebraicGeometry.NumericalType.TopologicalGenus
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex
public import ReasLib.AlgebraicGeometry.NumericalType.Diagonal
public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionBounds
public import ReasLib.AlgebraicGeometry.NumericalType.ProperSubgraphClassification

@[expose] public section

namespace NumericalType

/-- The non-`(-2)` indices of a minimal numerical type of genus `g ≥ 2` have
cardinality at most `2 * g - 2` when the type has more than one index. -/
public theorem nonMinusTwoIndexCardBound (g : ℤ) (hg : 2 ≤ g) (T : NumericalType)
    (hgenus : T.genus = g) (hminimal : T.IsMinimal) (hn : 1 < T.n) :
    (Set.ncard {j : Fin T.n |
      ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j} : ℤ) ≤ 2 * g - 2 := sorry

/-- Every non-`(-2)` index of a minimal numerical type of genus `g ≥ 2` has
component genus strictly less than `g` when the type has more than one index. -/
public theorem componentGenusBoundOfNotMinusTwo (g : ℤ) (hg : 2 ≤ g)
    (T : NumericalType) (hgenus : T.genus = g) (hminimal : T.IsMinimal) (hn : 1 < T.n)
    (j : Fin T.n)
    (hj : ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j) :
    (T.componentGenus j : ℤ) < g := sorry

/-- The multiplicity-weighted absolute diagonal intersection at a non-`(-2)` index
of a minimal numerical type of genus `g ≥ 2` is at most `6 * g - 6`. -/
public theorem diagonalBoundOfNotMinusTwo (g : ℤ) (hg : 2 ≤ g) (T : NumericalType)
    (hgenus : T.genus = g) (hminimal : T.IsMinimal) (hn : 1 < T.n) (j : Fin T.n)
    (hj : ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j) :
    (T.multiplicity j : ℤ) * |T.intersection j j| ≤ 6 * g - 6 := sorry

/-- For a non-`(-2)` target index `j` of a minimal numerical type of genus `g ≥ 2`,
every multiplicity-weighted intersection with `j` is at most `6 * g - 6`. -/
public theorem intersectionBoundOfNotMinusTwo (g : ℤ) (hg : 2 ≤ g)
    (T : NumericalType) (hgenus : T.genus = g) (hminimal : T.IsMinimal) (hn : 1 < T.n)
    (j : Fin T.n) (hj : ¬ IsMinusTwoIndex T.componentGenus T.weight T.intersection j)
    (i : Fin T.n) :
    (T.multiplicity i : ℤ) * T.intersection i j ≤ 6 * g - 6 := sorry

/-- The genus of a minimal numerical type with more than one index is at least
its topological genus. -/
public theorem topologicalGenus_le_genus (T : NumericalType) (hminimal : T.IsMinimal)
    (hn : 1 < T.n) : (T.topologicalGenus : ℤ) ≤ T.genus := sorry

/-- For a minimal numerical type of genus `g ≥ 2`, every multiplicity-weighted
absolute intersection is at most `768 * g`. -/
public theorem absoluteIntersectionBound (g : ℤ) (hg : 2 ≤ g) (T : NumericalType)
    (hgenus : T.genus = g) (hminimal : T.IsMinimal) (i j : Fin T.n) :
    (T.multiplicity i : ℤ) * |T.intersection i j| ≤ 768 * g := sorry

end NumericalType
