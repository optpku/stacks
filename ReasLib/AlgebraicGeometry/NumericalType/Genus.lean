/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.Equivalence
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Ring.Int.Parity

@[expose] public section

open scoped BigOperators

namespace NumericalType

/-- The multiplicity-weighted sum of the diagonal intersection numbers of a
numerical type is even. -/
public theorem multiplicityDiagonalSum_even (T : NumericalType) :
    Even (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) := sorry

/-- The rational genus expression associated to a numerical type is the cast
of an integer. -/
public theorem genusExpression_isInteger (T : NumericalType) :
    ∃ g : ℤ, (g : ℚ) =
      1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) := sorry

/-- The genus of a numerical type, computed as an integer using the even total
diagonal contribution. -/
public def genus (T : NumericalType) : ℤ :=
  1 + ∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
      ((T.componentGenus i : ℤ) - 1) -
    (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2

/-- The integer formula computing the genus of a numerical type. -/
public theorem genus_def (T : NumericalType) :
    T.genus =
      1 + ∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) -
        (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2 := sorry

/-- Casting the genus to `ℚ` gives the rational genus expression. -/
public theorem genus_cast (T : NumericalType) :
    (T.genus : ℚ) =
      1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) := sorry

/-- An integer is the genus exactly when its cast is the rational genus expression. -/
public theorem genus_eq_iff (T : NumericalType) (g : ℤ) :
    T.genus = g ↔
      (g : ℚ) = 1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) := sorry

namespace IsRelabeling

/-- Relabeling a numerical type preserves its genus. -/
public theorem genus_eq {T T' : NumericalType} {e : Fin T.n ≃ Fin T'.n}
    (h : IsRelabeling T T' e) : T.genus = T'.genus := sorry

end IsRelabeling

end NumericalType
