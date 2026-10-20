module

public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.Diagonal
public import Mathlib.Data.Rat.Defs

namespace NumericalType

/-- The property that an index has component genus zero and diagonal entry equal to
the negative of its weight. -/
public structure IsMinusOneIndex {n : ℕ} (componentGenus weight : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Prop where
  /-- The component at a `(-1)`-index has genus zero. -/
  genus_eq_zero : componentGenus i = 0
  /-- The diagonal entry at a `(-1)`-index is the negative of its weight. -/
  diag_eq_neg_weight : intersection i i = -(weight i : ℤ)

namespace IsMinusOneIndex

set_option linter.defProp false in
/-- Construct the `(-1)`-index property from its two defining equations. -/
public def ofEquations {n : ℕ} {componentGenus weight : Fin n → ℕ}
    {intersection : Matrix (Fin n) (Fin n) ℤ} {i : Fin n}
    (genus_eq_zero : componentGenus i = 0)
    (diag_eq_neg_weight : intersection i i = -(weight i : ℤ)) :
    IsMinusOneIndex componentGenus weight intersection i := sorry

/-- The `(-1)`-index property is preserved when all numerical data are reindexed by
a permutation. -/
public theorem reindex_iff {n : ℕ} (componentGenus weight : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    IsMinusOneIndex (componentGenus ∘ e) (weight ∘ e)
        (intersection.submatrix e e) i ↔
      IsMinusOneIndex componentGenus weight intersection (e i) := sorry

end IsMinusOneIndex

/-- An index is a `(-1)`-index exactly when its component genus is zero and its
diagonal intersection is the negative of its weight. -/
public theorem isMinusOneIndex_iff {n : ℕ} (componentGenus weight : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    IsMinusOneIndex componentGenus weight intersection i ↔
      componentGenus i = 0 ∧ intersection i i = -(weight i : ℤ) := sorry

/-- If a genus contribution of a numerical type with more than one index is
negative, then the index has component genus zero and diagonal intersection
equal to the negative of its weight. -/
public theorem isMinusOneIndex_of_contribution_neg (T : NumericalType) (hn : 1 < T.n)
    (i : Fin T.n)
    (hcontribution :
      (T.multiplicity i : ℚ) *
          ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
            (T.intersection i i : ℚ) / 2) < 0) :
    IsMinusOneIndex T.componentGenus T.weight T.intersection i := sorry

end NumericalType
