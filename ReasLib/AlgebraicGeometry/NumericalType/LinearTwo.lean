module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

/-- The three possible weighted linear configurations obtained by restricting a
numerical type to two ordered indices. -/
public def NumericalType.IsLinearTwoConfiguration (T : NumericalType)
    (v : Fin 2 ↪ Fin T.n) : Prop :=
  (T.weight ∘ v = ![T.weight (v 0), T.weight (v 0)] ∧
      T.intersection.submatrix v v =
        ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0)],
          ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ))]] ∧
      2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
      2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0)) ∨
    (T.weight ∘ v = ![T.weight (v 0), 2 * T.weight (v 0)] ∧
      T.intersection.submatrix v v =
        ![![-(2 * (T.weight (v 0) : ℤ)), 2 * (T.weight (v 0) : ℤ)],
          ![2 * (T.weight (v 0) : ℤ), -(4 * (T.weight (v 0) : ℤ))]] ∧
      T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
      2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0)) ∨
    (T.weight ∘ v = ![T.weight (v 0), 3 * T.weight (v 0)] ∧
      T.intersection.submatrix v v =
        ![![-(2 * (T.weight (v 0) : ℤ)), 3 * (T.weight (v 0) : ℤ)],
          ![3 * (T.weight (v 0) : ℤ), -(6 * (T.weight (v 0) : ℤ))]] ∧
      2 * T.multiplicity (v 0) ≥ 3 * T.multiplicity (v 1) ∧
      2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0))

/-- In a numerical type with more than two indices, two distinct `(-2)`-indices
with positive intersection have, up to reordering, one of the three weighted
linear configurations. -/
public theorem NumericalType.linearTwoClassification (T : NumericalType) (hn : 2 < T.n)
    (v : Fin 2 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hmeet : 0 < T.intersection (v 0) (v 1)) :
    ∃ p : Equiv.Perm (Fin 2),
      NumericalType.IsLinearTwoConfiguration T (p.toEmbedding.trans v) := sorry
