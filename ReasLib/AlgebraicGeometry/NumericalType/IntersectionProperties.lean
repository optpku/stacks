module

public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.Graph
public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionForm
public import ReasLib.LinearAlgebra.Matrix.NegativeSemidefinite

@[expose] public section

open scoped BigOperators

namespace NumericalType

/-- Distinct indices have nonnegative intersection, and zero intersection is equivalent to non-adjacency in the positive-intersection graph. -/
public theorem intersection_offDiagonal_nonnegative (T : NumericalType) :
    ∀ i j : Fin T.n, i ≠ j →
      0 ≤ T.intersection i j ∧
        (T.intersection i j = 0 ↔ ¬ T.intersectionGraph.Adj i j) := sorry

/-- The multiplicity vector is orthogonal to every column of the intersection matrix. -/
public theorem weighted_intersection_eq_zero (T : NumericalType) :
    ∀ j : Fin T.n, ∑ i, (T.multiplicity i : ℤ) * T.intersection i j = 0 := sorry

/-- No nonempty proper subset of indices is disconnected from its complement in the intersection matrix. -/
public theorem intersection_no_disconnected_subset (T : NumericalType) :
    ¬ ∃ I : Set (Fin T.n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ i ∈ I, ∀ j ∉ I, T.intersection i j = 0 := sorry

/-- The integral intersection form is nonpositive on every coefficient vector. -/
public theorem intersectionForm_nonpos (T : NumericalType) :
    ∀ a : Fin T.n → ℤ, T.intersectionForm a a ≤ 0 := sorry

/-- Equality in the nonpositivity of the integral intersection form holds exactly for rational multiples of the multiplicity vector. -/
public theorem intersectionForm_eq_zero_iff (T : NumericalType) :
    ∀ a : Fin T.n → ℤ,
      T.intersectionForm a a = 0 ↔
        ∃ q : ℚ, ∀ i, (a i : ℚ) = q * (T.multiplicity i : ℚ) := sorry

end NumericalType
