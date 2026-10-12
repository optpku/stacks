/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Equivalence
public import ReasLib.AlgebraicGeometry.NumericalType.Genus
public import ReasLib.AlgebraicGeometry.NumericalType.MinusOneIndex

namespace NumericalType

/-- A numerical type is minimal when none of its indices is a `(-1)`-index. -/
public def IsMinimal (T : NumericalType) : Prop :=
  ¬ ∃ i, IsMinusOneIndex T.componentGenus T.weight T.intersection i

/-- Minimality is equivalent to the absence of an index of component genus zero
whose diagonal intersection is the negative of its weight. -/
public theorem isMinimal_iff (T : NumericalType) :
    T.IsMinimal ↔
      ¬ ∃ i, T.componentGenus i = 0 ∧ T.intersection i i = -(T.weight i : ℤ) := sorry

namespace IsMinimal

/-- A minimal numerical type has no `(-1)`-index. -/
public theorem not_isMinusOneIndex {T : NumericalType} (h : T.IsMinimal)
    (i : Fin T.n) :
    ¬ IsMinusOneIndex T.componentGenus T.weight T.intersection i := sorry

end IsMinimal

namespace IsRelabeling

/-- Data-preserving relabeling preserves minimality. -/
public theorem isMinimal_iff {T T' : NumericalType} {e : Fin T.n ≃ Fin T'.n}
    (h : IsRelabeling T T' e) : T.IsMinimal ↔ T'.IsMinimal := sorry

end IsRelabeling

/-- A minimal numerical type with more than one index has genus at least one. -/
public theorem one_le_genus (T : NumericalType) (hminimal : T.IsMinimal) (hn : 1 < T.n) :
    1 ≤ T.genus := sorry

end NumericalType
