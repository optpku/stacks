/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

/-- The four possible weighted linear configurations obtained by restricting a
numerical type to four ordered indices. -/
public def NumericalType.IsLinearFourConfiguration (T : NumericalType)
    (v : Fin 4 ↪ Fin T.n) : Prop :=
  (T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0), T.weight (v 0)] ∧
    T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0)],
        ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥
      T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥
      T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2)) ∨
  (T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0),
        2 * T.weight (v 0)] ∧
    T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          2 * (T.weight (v 0) : ℤ)],
        ![0, 0, 2 * (T.weight (v 0) : ℤ),
          -(4 * (T.weight (v 0) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥
      T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥
      T.multiplicity (v 1) + 2 * T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2)) ∨
  (T.weight ∘ v =
      ![2 * T.weight (v 3), 2 * T.weight (v 3),
        2 * T.weight (v 3), T.weight (v 3)] ∧
    T.intersection.submatrix v v =
      ![![-(4 * (T.weight (v 3) : ℤ)), 2 * (T.weight (v 3) : ℤ), 0, 0],
        ![2 * (T.weight (v 3) : ℤ), -(4 * (T.weight (v 3) : ℤ)),
          2 * (T.weight (v 3) : ℤ), 0],
        ![0, 2 * (T.weight (v 3) : ℤ), -(4 * (T.weight (v 3) : ℤ)),
          2 * (T.weight (v 3) : ℤ)],
        ![0, 0, 2 * (T.weight (v 3) : ℤ),
          -(2 * (T.weight (v 3) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥
      T.multiplicity (v 0) + T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥
      T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    T.multiplicity (v 3) ≥ T.multiplicity (v 2)) ∨
  (T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0),
        2 * T.weight (v 0), 2 * T.weight (v 0)] ∧
    T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          2 * (T.weight (v 0) : ℤ), 0],
        ![0, 2 * (T.weight (v 0) : ℤ), -(4 * (T.weight (v 0) : ℤ)),
          2 * (T.weight (v 0) : ℤ)],
        ![0, 0, 2 * (T.weight (v 0) : ℤ),
          -(4 * (T.weight (v 0) : ℤ))]] ∧
    2 * T.multiplicity (v 0) ≥ T.multiplicity (v 1) ∧
    2 * T.multiplicity (v 1) ≥
      T.multiplicity (v 0) + 2 * T.multiplicity (v 2) ∧
    2 * T.multiplicity (v 2) ≥
      T.multiplicity (v 1) + T.multiplicity (v 3) ∧
    2 * T.multiplicity (v 3) ≥ T.multiplicity (v 2))

namespace NumericalType

/-- Four distinct `(-2)`-indices joined successively in a numerical type with more
than four indices satisfy one of the four weighted linear configurations after a
permutation of the indices. -/
theorem linearFourClassification (T : NumericalType) (hn : 4 < T.n)
    (v : Fin 4 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hchain : ∀ r : Fin 3,
      T.intersection (v r.castSucc) (v r.succ) ≠ 0) :
    ∃ p : Equiv.Perm (Fin 4),
      IsLinearFourConfiguration T (p.toEmbedding.trans v) := sorry

end NumericalType
