module

public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.LinearAlgebra.Matrix.NegativeSemidefinite

namespace NumericalType

/-- Every diagonal entry of a numerical type with more than one index is
strictly negative. -/
public theorem diagonal_neg (T : NumericalType) (hn : 1 < T.n) (i : Fin T.n) :
    T.intersection i i < 0 := sorry

end NumericalType
