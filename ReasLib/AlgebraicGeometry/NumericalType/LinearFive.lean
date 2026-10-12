/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

/-- The three possible weighted linear configurations obtained by restricting a
numerical type to five ordered indices. -/
public def IsLinearFiveConfiguration (T : NumericalType) (v : Fin 5 ↪ Fin T.n) : Prop :=
  (T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0),
        T.weight (v 0), T.weight (v 0)] ∧
    T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, 0],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0],
        ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0)],
        ![0, 0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥ T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2) + T.multiplicity (v 4) ∧
    2 * T.multiplicity (v 4) ≥ T.multiplicity (v 3)) ∨
  (T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0),
        T.weight (v 0), 2 * T.weight (v 0)] ∧
    T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, 0],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0],
        ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          2 * (T.weight (v 0) : ℤ)],
        ![0, 0, 0, 2 * (T.weight (v 0) : ℤ),
          -(4 * (T.weight (v 0) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥ T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2) + 2 * T.multiplicity (v 4) ∧
    2 * T.multiplicity (v 4) ≥ T.multiplicity (v 3)) ∨
  (T.weight ∘ v =
      ![2 * T.weight (v 4), 2 * T.weight (v 4), 2 * T.weight (v 4),
        2 * T.weight (v 4), T.weight (v 4)] ∧
    T.intersection.submatrix v v =
      ![![-(4 * (T.weight (v 4) : ℤ)), 2 * (T.weight (v 4) : ℤ), 0, 0, 0],
        ![2 * (T.weight (v 4) : ℤ), -(4 * (T.weight (v 4) : ℤ)),
          2 * (T.weight (v 4) : ℤ), 0, 0],
        ![0, 2 * (T.weight (v 4) : ℤ), -(4 * (T.weight (v 4) : ℤ)),
          2 * (T.weight (v 4) : ℤ), 0],
        ![0, 0, 2 * (T.weight (v 4) : ℤ), -(4 * (T.weight (v 4) : ℤ)),
          2 * (T.weight (v 4) : ℤ)],
        ![0, 0, 0, 2 * (T.weight (v 4) : ℤ),
          -(2 * (T.weight (v 4) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥ T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥ T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2) + T.multiplicity (v 4) ∧
    T.multiplicity (v 3) ≥ T.multiplicity (v 2))

/-- In a numerical type with more than five indices, five distinct
`(-2)`-indices joined successively have, up to reordering, one of the three
weighted linear configurations. -/
public theorem linearFiveClassification (T : NumericalType) (hn : 5 < T.n)
    (v : Fin 5 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hchain : ∀ r : Fin 4,
      T.intersection (v r.castSucc) (v r.succ) ≠ 0) :
    ∃ p : Equiv.Perm (Fin 5),
      IsLinearFiveConfiguration T (p.toEmbedding.trans v) := sorry

end NumericalType
