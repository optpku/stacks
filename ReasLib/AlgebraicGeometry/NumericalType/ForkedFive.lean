module

import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

/-- The weighted five-vertex fork configuration, with branch vertex `2`. -/
public structure IsForkedFiveConfiguration (T : NumericalType)
    (v : Fin 5 ↪ Fin T.n) : Prop where
  /-- All five selected indices have the weight of the first selected index. -/
  weight_eq : T.weight ∘ v =
    ![T.weight (v 0), T.weight (v 0), T.weight (v 0),
      T.weight (v 0), T.weight (v 0)]
  /-- The restricted intersection matrix is the weighted five-vertex fork matrix. -/
  intersection_eq : T.intersection.submatrix v v =
    ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0],
      ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), 0, 0],
      ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
        T.weight (v 0), T.weight (v 0)],
      ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), 0],
      ![0, 0, (T.weight (v 0) : ℤ), 0, -(2 * (T.weight (v 0) : ℤ))]]
  /-- The multiplicity inequality at the left endpoint. -/
  leftEndpoint_le : T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0)
  /-- The multiplicity inequality at the second vertex. -/
  leftInner_le : T.multiplicity (v 0) + T.multiplicity (v 2) ≤
    2 * T.multiplicity (v 1)
  /-- The multiplicity inequality at the three-neighbor branch vertex. -/
  branch_le : T.multiplicity (v 1) + T.multiplicity (v 3) +
    T.multiplicity (v 4) ≤ 2 * T.multiplicity (v 2)
  /-- The multiplicity inequality at the first branch endpoint. -/
  firstBranchEndpoint_le : T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 3)
  /-- The multiplicity inequality at the second branch endpoint. -/
  secondBranchEndpoint_le : T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 4)

namespace IsForkedFiveConfiguration

set_option linter.defProp false in
/-- Construct a five-vertex fork configuration from its displayed conditions. -/
public def ofConditions {T : NumericalType} {v : Fin 5 ↪ Fin T.n}
    (weight_eq : T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0),
        T.weight (v 0), T.weight (v 0)])
    (intersection_eq : T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), 0, 0, 0],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), 0, 0],
        ![0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)),
          T.weight (v 0), T.weight (v 0)],
        ![0, 0, (T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), 0],
        ![0, 0, (T.weight (v 0) : ℤ), 0, -(2 * (T.weight (v 0) : ℤ))]])
    (leftEndpoint_le : T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0))
    (leftInner_le : T.multiplicity (v 0) + T.multiplicity (v 2) ≤
      2 * T.multiplicity (v 1))
    (branch_le : T.multiplicity (v 1) + T.multiplicity (v 3) +
      T.multiplicity (v 4) ≤ 2 * T.multiplicity (v 2))
    (firstBranchEndpoint_le : T.multiplicity (v 2) ≤
      2 * T.multiplicity (v 3))
    (secondBranchEndpoint_le : T.multiplicity (v 2) ≤
      2 * T.multiplicity (v 4)) :
    IsForkedFiveConfiguration T v := sorry

end IsForkedFiveConfiguration

/-- Five distinct `(-2)`-indices forming a five-vertex fork in a numerical type
with more than five indices have the displayed configuration after reordering. -/
public theorem forkedFiveClassification (T : NumericalType) (hn : 5 < T.n)
    (v : Fin 5 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (h₁₂ : T.intersection (v 0) (v 1) ≠ 0)
    (h₂₃ : T.intersection (v 1) (v 2) ≠ 0)
    (h₃₄ : T.intersection (v 2) (v 3) ≠ 0)
    (h₃₅ : T.intersection (v 2) (v 4) ≠ 0) :
    ∃ p : Equiv.Perm (Fin 5),
      IsForkedFiveConfiguration T (p.toEmbedding.trans v) := sorry

end NumericalType
