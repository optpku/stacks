module

import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

/-- The weighted forked configuration on seven ordered indices, with branch vertex `3`. -/
public structure IsForkedSevenConfiguration (T : NumericalType)
    (v : Fin 7 ↪ Fin T.n) : Prop where
  /-- All seven selected indices have the weight of the first selected index. -/
  weight_eq : T.weight ∘ v =
    ![T.weight (v 0), T.weight (v 0), T.weight (v 0), T.weight (v 0),
      T.weight (v 0), T.weight (v 0), T.weight (v 0)]
  /-- The restricted intersection matrix is the weighted forked matrix. -/
  intersection_eq : T.intersection.submatrix v v =
    ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0, 0, 0],
      ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), 0, 0, 0, 0],
      ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), 0, 0, 0],
      ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), 0, T.weight (v 0)],
      ![0, 0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), 0],
      ![0, 0, 0, 0, (T.weight (v 0) : ℤ),
        -(2 * (T.weight (v 0) : ℤ)), 0],
      ![0, 0, 0, (T.weight (v 0) : ℤ), 0, 0,
        -(2 * (T.weight (v 0) : ℤ))]]
  /-- The multiplicity inequality at the left endpoint. -/
  leftEndpoint_le : T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0)
  /-- The multiplicity inequality at the second vertex. -/
  leftInner_le : T.multiplicity (v 0) + T.multiplicity (v 2) ≤
    2 * T.multiplicity (v 1)
  /-- The multiplicity inequality at the third vertex. -/
  leftBranch_le : T.multiplicity (v 1) + T.multiplicity (v 3) ≤
    2 * T.multiplicity (v 2)
  /-- The multiplicity inequality at the three-neighbor branch vertex. -/
  branch_le : T.multiplicity (v 2) + T.multiplicity (v 4) +
    T.multiplicity (v 6) ≤ 2 * T.multiplicity (v 3)
  /-- The multiplicity inequality at the fifth vertex. -/
  rightInner_le : T.multiplicity (v 3) + T.multiplicity (v 5) ≤
    2 * T.multiplicity (v 4)
  /-- The multiplicity inequality at the right endpoint. -/
  rightEndpoint_le : T.multiplicity (v 4) ≤ 2 * T.multiplicity (v 5)
  /-- The multiplicity inequality at the branch endpoint. -/
  branchEndpoint_le : T.multiplicity (v 3) ≤ 2 * T.multiplicity (v 6)

namespace IsForkedSevenConfiguration

set_option linter.defProp false in
/-- Construct a forked seven-vertex configuration from its displayed conditions. -/
public def ofConditions {T : NumericalType} {v : Fin 7 ↪ Fin T.n}
    (weight_eq : T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0), T.weight (v 0),
        T.weight (v 0), T.weight (v 0), T.weight (v 0)])
    (intersection_eq : T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0, 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, 0, 0, 0],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, 0, 0],
        ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, T.weight (v 0)],
        ![0, 0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0],
        ![0, 0, 0, 0, (T.weight (v 0) : ℤ),
          -(2 * (T.weight (v 0) : ℤ)), 0],
        ![0, 0, 0, (T.weight (v 0) : ℤ), 0, 0,
          -(2 * (T.weight (v 0) : ℤ))]])
    (leftEndpoint_le : T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0))
    (leftInner_le : T.multiplicity (v 0) + T.multiplicity (v 2) ≤
      2 * T.multiplicity (v 1))
    (leftBranch_le : T.multiplicity (v 1) + T.multiplicity (v 3) ≤
      2 * T.multiplicity (v 2))
    (branch_le : T.multiplicity (v 2) + T.multiplicity (v 4) +
      T.multiplicity (v 6) ≤ 2 * T.multiplicity (v 3))
    (rightInner_le : T.multiplicity (v 3) + T.multiplicity (v 5) ≤
      2 * T.multiplicity (v 4))
    (rightEndpoint_le : T.multiplicity (v 4) ≤ 2 * T.multiplicity (v 5))
    (branchEndpoint_le : T.multiplicity (v 3) ≤ 2 * T.multiplicity (v 6)) :
    IsForkedSevenConfiguration T v := sorry

end IsForkedSevenConfiguration

/-- Seven distinct `(-2)`-indices forming a forked chain in a numerical type with
more than seven indices have a common weight, the forked intersection matrix,
and the seven multiplicity inequalities. -/
public theorem forkedSevenClassification (T : NumericalType) (hn : 7 < T.n)
    (v : Fin 7 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (h₁₂ : T.intersection (v 0) (v 1) ≠ 0)
    (h₂₃ : T.intersection (v 1) (v 2) ≠ 0)
    (h₃₄ : T.intersection (v 2) (v 3) ≠ 0)
    (h₄₅ : T.intersection (v 3) (v 4) ≠ 0)
    (h₅₆ : T.intersection (v 4) (v 5) ≠ 0)
    (h₄₇ : T.intersection (v 3) (v 6) ≠ 0) :
    IsForkedSevenConfiguration T v := sorry

end NumericalType
