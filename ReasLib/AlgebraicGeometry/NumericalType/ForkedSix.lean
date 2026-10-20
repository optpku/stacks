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

namespace NumericalType

/-- The weighted forked configuration on six ordered indices, with branch vertex `2`. -/
public structure IsForkedSixConfiguration (T : NumericalType)
    (v : Fin 6 ↪ Fin T.n) : Prop where
  /-- All six selected indices have the weight of the first selected index. -/
  weight_eq : T.weight ∘ v =
    ![T.weight (v 0), T.weight (v 0), T.weight (v 0),
      T.weight (v 0), T.weight (v 0), T.weight (v 0)]
  /-- The restricted intersection matrix is the weighted forked matrix. -/
  intersection_eq : T.intersection.submatrix v v =
    ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0, 0],
      ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), 0, 0, 0],
      ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), 0, T.weight (v 0)],
      ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), 0],
      ![0, 0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), 0],
      ![0, 0, (T.weight (v 0) : ℤ), 0, 0,
        -(2 * (T.weight (v 0) : ℤ))]]
  /-- The multiplicity inequality at the left endpoint. -/
  leftEndpoint_le : T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0)
  /-- The multiplicity inequality at the second vertex. -/
  leftInner_le : T.multiplicity (v 0) + T.multiplicity (v 2) ≤
    2 * T.multiplicity (v 1)
  /-- The multiplicity inequality at the three-neighbor branch vertex. -/
  branch_le : T.multiplicity (v 1) + T.multiplicity (v 3) +
    T.multiplicity (v 5) ≤ 2 * T.multiplicity (v 2)
  /-- The multiplicity inequality at the fourth vertex. -/
  rightInner_le : T.multiplicity (v 2) + T.multiplicity (v 4) ≤
    2 * T.multiplicity (v 3)
  /-- The multiplicity inequality at the right endpoint. -/
  rightEndpoint_le : T.multiplicity (v 3) ≤ 2 * T.multiplicity (v 4)
  /-- The multiplicity inequality at the branch endpoint. -/
  branchEndpoint_le : T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 5)

namespace IsForkedSixConfiguration

set_option linter.defProp false in
/-- Construct a forked six-vertex configuration from its displayed conditions. -/
public def ofConditions {T : NumericalType} {v : Fin 6 ↪ Fin T.n}
    (weight_eq : T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0),
        T.weight (v 0), T.weight (v 0), T.weight (v 0)])
    (intersection_eq : T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, 0, 0],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, T.weight (v 0)],
        ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0],
        ![0, 0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), 0],
        ![0, 0, (T.weight (v 0) : ℤ), 0, 0,
          -(2 * (T.weight (v 0) : ℤ))]])
    (leftEndpoint_le : T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0))
    (leftInner_le : T.multiplicity (v 0) + T.multiplicity (v 2) ≤
      2 * T.multiplicity (v 1))
    (branch_le : T.multiplicity (v 1) + T.multiplicity (v 3) +
      T.multiplicity (v 5) ≤ 2 * T.multiplicity (v 2))
    (rightInner_le : T.multiplicity (v 2) + T.multiplicity (v 4) ≤
      2 * T.multiplicity (v 3))
    (rightEndpoint_le : T.multiplicity (v 3) ≤ 2 * T.multiplicity (v 4))
    (branchEndpoint_le : T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 5)) :
    IsForkedSixConfiguration T v :=
  { weight_eq, intersection_eq, leftEndpoint_le, leftInner_le, branch_le,
    rightInner_le, rightEndpoint_le, branchEndpoint_le }

/-- A forked six-vertex configuration is equivalent to its common-weight equation,
restricted intersection matrix equation, and six multiplicity inequalities. -/
public theorem conditions_iff {T : NumericalType} {v : Fin 6 ↪ Fin T.n} :
    IsForkedSixConfiguration T v ↔
      (T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0),
        T.weight (v 0), T.weight (v 0), T.weight (v 0)]) ∧
      (T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, 0, 0],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, T.weight (v 0)],
        ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0],
        ![0, 0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), 0],
        ![0, 0, (T.weight (v 0) : ℤ), 0, 0,
          -(2 * (T.weight (v 0) : ℤ))]]) ∧
      (T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0)) ∧
      (T.multiplicity (v 0) + T.multiplicity (v 2) ≤
      2 * T.multiplicity (v 1)) ∧
      (T.multiplicity (v 1) + T.multiplicity (v 3) +
      T.multiplicity (v 5) ≤ 2 * T.multiplicity (v 2)) ∧
      (T.multiplicity (v 2) + T.multiplicity (v 4) ≤
      2 * T.multiplicity (v 3)) ∧
      (T.multiplicity (v 3) ≤ 2 * T.multiplicity (v 4)) ∧
      (T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 5)) := by
  constructor
  · intro h
    exact ⟨h.weight_eq, h.intersection_eq, h.leftEndpoint_le, h.leftInner_le,
      h.branch_le, h.rightInner_le, h.rightEndpoint_le, h.branchEndpoint_le⟩
  · rintro ⟨weight_eq, intersection_eq, leftEndpoint_le, leftInner_le,
      branch_le, rightInner_le, rightEndpoint_le, branchEndpoint_le⟩
    exact ofConditions weight_eq intersection_eq leftEndpoint_le leftInner_le
      branch_le rightInner_le rightEndpoint_le branchEndpoint_le

end IsForkedSixConfiguration

/-- Six distinct `(-2)`-indices forming the specified forked chain in a numerical
type with more than six indices have a common weight, the weighted forked
intersection matrix, and the six vertex multiplicity inequalities. -/
public theorem forkedSixClassification (T : NumericalType) (hn : 6 < T.n)
    (v : Fin 6 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (h₁₂ : T.intersection (v 0) (v 1) ≠ 0)
    (h₂₃ : T.intersection (v 1) (v 2) ≠ 0)
    (h₃₄ : T.intersection (v 2) (v 3) ≠ 0)
    (h₄₅ : T.intersection (v 3) (v 4) ≠ 0)
    (h₃₆ : T.intersection (v 2) (v 5) ≠ 0) :
    IsForkedSixConfiguration T v := sorry

end NumericalType
