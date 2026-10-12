/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

/-- The three possible weighted linear configurations obtained by restricting a
numerical type to three ordered indices. -/
public def IsLinearThreeConfiguration (T : NumericalType)
    (v : Fin 3 ↪ Fin T.n) : Prop :=
  (T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0)] ∧
    T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), T.weight (v 0)],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥
      T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥ T.multiplicity (v 1)) ∨
  (T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), 2 * T.weight (v 0)] ∧
    T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          2 * (T.weight (v 0) : ℤ)],
        ![0, 2 * (T.weight (v 0) : ℤ), -(4 * (T.weight (v 0) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥
      T.multiplicity (v 0) + 2 * T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥ T.multiplicity (v 1)) ∨
  (T.weight ∘ v =
      ![2 * T.weight (v 2), 2 * T.weight (v 2), T.weight (v 2)] ∧
    T.intersection.submatrix v v =
      ![![-(4 * (T.weight (v 2) : ℤ)), 2 * (T.weight (v 2) : ℤ), 0],
        ![2 * (T.weight (v 2) : ℤ), -(4 * (T.weight (v 2) : ℤ)),
          2 * (T.weight (v 2) : ℤ)],
        ![0, 2 * (T.weight (v 2) : ℤ), -(2 * (T.weight (v 2) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥
      T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    T.multiplicity (v 2) ≥ T.multiplicity (v 1))

/-- A numerical type with more than three indices contains, after reordering,
one of the three weighted linear configurations whenever three selected
`(-2)`-indices have at least two nonzero pairwise intersections. -/
public theorem linearThreeClassification (T : NumericalType) (hn : 3 < T.n)
    (v : Fin 3 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (htwo :
      (T.intersection (v 0) (v 1) ≠ 0 ∧ T.intersection (v 0) (v 2) ≠ 0) ∨
      (T.intersection (v 0) (v 1) ≠ 0 ∧ T.intersection (v 1) (v 2) ≠ 0) ∨
      (T.intersection (v 0) (v 2) ≠ 0 ∧ T.intersection (v 1) (v 2) ≠ 0)) :
    ∃ p : Equiv.Perm (Fin 3),
      IsLinearThreeConfiguration T (p.toEmbedding.trans v) := sorry

end NumericalType
