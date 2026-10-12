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

/-- The weighted four-vertex fork configuration, with central vertex `0`. -/
public structure IsForkedFourConfiguration (T : NumericalType)
    (v : Fin 4 ↪ Fin T.n) : Prop where
  /-- All four selected indices have the weight of the central index. -/
  weight_eq : T.weight ∘ v =
    ![T.weight (v 0), T.weight (v 0), T.weight (v 0), T.weight (v 0)]
  /-- The restricted intersection matrix is the weighted four-vertex fork matrix. -/
  intersection_eq : T.intersection.submatrix v v =
    ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), T.weight (v 0),
        T.weight (v 0)],
      ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), 0, 0],
      ![(T.weight (v 0) : ℤ), 0, -(2 * (T.weight (v 0) : ℤ)), 0],
      ![(T.weight (v 0) : ℤ), 0, 0, -(2 * (T.weight (v 0) : ℤ))]]
  /-- The sum of the leaf multiplicities is at most twice the central multiplicity. -/
  branch_le : T.multiplicity (v 1) + T.multiplicity (v 2) +
    T.multiplicity (v 3) ≤ 2 * T.multiplicity (v 0)
  /-- The central multiplicity is at most twice the first leaf multiplicity. -/
  firstLeaf_le : T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 1)
  /-- The central multiplicity is at most twice the second leaf multiplicity. -/
  secondLeaf_le : T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 2)
  /-- The central multiplicity is at most twice the third leaf multiplicity. -/
  thirdLeaf_le : T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 3)

namespace IsForkedFourConfiguration

set_option linter.defProp false in
/-- Construct a four-vertex fork configuration from its displayed conditions. -/
public def ofConditions {T : NumericalType} {v : Fin 4 ↪ Fin T.n}
    (weight_eq : T.weight ∘ v =
      ![T.weight (v 0), T.weight (v 0), T.weight (v 0), T.weight (v 0)])
    (intersection_eq : T.intersection.submatrix v v =
      ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), T.weight (v 0),
          T.weight (v 0)],
        ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), 0, 0],
        ![(T.weight (v 0) : ℤ), 0, -(2 * (T.weight (v 0) : ℤ)), 0],
        ![(T.weight (v 0) : ℤ), 0, 0, -(2 * (T.weight (v 0) : ℤ))]])
    (branch_le : T.multiplicity (v 1) + T.multiplicity (v 2) +
      T.multiplicity (v 3) ≤ 2 * T.multiplicity (v 0))
    (firstLeaf_le : T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 1))
    (secondLeaf_le : T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 2))
    (thirdLeaf_le : T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 3)) :
    IsForkedFourConfiguration T v :=
  ⟨weight_eq, intersection_eq, branch_le, firstLeaf_le, secondLeaf_le, thirdLeaf_le⟩

/-- The four-vertex fork configuration is equivalent to its six defining conditions. -/
public theorem conditions_iff {T : NumericalType} {v : Fin 4 ↪ Fin T.n} :
    IsForkedFourConfiguration T v ↔
      (T.weight ∘ v =
          ![T.weight (v 0), T.weight (v 0), T.weight (v 0), T.weight (v 0)]) ∧
      (T.intersection.submatrix v v =
          ![![-(2 * (T.weight (v 0) : ℤ)), T.weight (v 0), T.weight (v 0),
              T.weight (v 0)],
            ![(T.weight (v 0) : ℤ), -(2 * (T.weight (v 0) : ℤ)), 0, 0],
            ![(T.weight (v 0) : ℤ), 0, -(2 * (T.weight (v 0) : ℤ)), 0],
            ![(T.weight (v 0) : ℤ), 0, 0, -(2 * (T.weight (v 0) : ℤ))]]) ∧
      (T.multiplicity (v 1) + T.multiplicity (v 2) +
          T.multiplicity (v 3) ≤ 2 * T.multiplicity (v 0)) ∧
      (T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 1)) ∧
      (T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 2)) ∧
      (T.multiplicity (v 0) ≤ 2 * T.multiplicity (v 3)) := sorry

end IsForkedFourConfiguration

/-- Four distinct `(-2)`-indices forming a three-leaf fork in a numerical type
with more than four indices have the displayed common weight, intersection
matrix, and multiplicity inequalities. -/
public theorem forkedFourClassification (T : NumericalType) (hn : 4 < T.n)
    (v : Fin 4 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₀₂ : T.intersection (v 0) (v 2) ≠ 0)
    (h₀₃ : T.intersection (v 0) (v 3) ≠ 0) :
    IsForkedFourConfiguration T v := sorry

namespace IsForkedFourConfiguration

/-- In a weighted four-vertex fork configuration, the central multiplicity is
at least the maximum of the three leaf multiplicities. -/
public theorem leafMax_le_center {T : NumericalType} {v : Fin 4 ↪ Fin T.n}
    (h : IsForkedFourConfiguration T v) :
    max (T.multiplicity (v 1))
      (max (T.multiplicity (v 2)) (T.multiplicity (v 3))) ≤
      T.multiplicity (v 0) := sorry

end IsForkedFourConfiguration

end NumericalType
