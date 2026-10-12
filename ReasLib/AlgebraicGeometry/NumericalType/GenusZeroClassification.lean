/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Minimality
public import ReasLib.AlgebraicGeometry.NumericalType.OneIndex

namespace NumericalType

/-- A minimal numerical type of genus zero has one index and the corresponding
indexed multiplicity, diagonal intersection, weight, and component genus. -/
public theorem genusZeroClassification
    (T : NumericalType) (hminimal : T.IsMinimal) (hgenus : T.genus = 0) :
    T.n = 1 ∧ ∀ i : Fin T.n,
      T.multiplicity i = 1 ∧ T.intersection i i = 0 ∧ T.weight i = 1 ∧
        T.componentGenus i = 0 := sorry

end NumericalType
