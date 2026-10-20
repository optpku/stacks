module

public import ReasLib.AlgebraicGeometry.NumericalType

@[expose] public section

namespace NumericalType

/-- A positive intersection, multiplied by its source multiplicity, is bounded by
the target multiplicity times the absolute target diagonal intersection. -/
public theorem positiveIntersectionBound (T : NumericalType) (i j : Fin T.n)
    (hij : 0 < T.intersection i j) :
    (T.multiplicity i : ℤ) * T.intersection i j ≤
      (T.multiplicity j : ℤ) * |T.intersection j j| := sorry

/-- When two indices have positive intersection, the source multiplicity times
its weight is bounded by the target multiplicity times the absolute target diagonal. -/
public theorem weightBoundOfPositiveIntersection (T : NumericalType) (i j : Fin T.n)
    (hij : 0 < T.intersection i j) :
    (T.multiplicity i : ℤ) * (T.weight i : ℤ) ≤
      (T.multiplicity j : ℤ) * |T.intersection j j| := sorry

end NumericalType
