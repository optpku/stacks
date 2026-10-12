/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType
public import Mathlib.Data.Rat.Defs

@[expose] public section

namespace NumericalType

/-- The property that an index has component genus zero and diagonal entry equal to
`-2` times its weight. -/
public structure IsMinusTwoIndex {n : ℕ} (componentGenus weight : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Prop where
  /-- The component at a `(-2)`-index has genus zero. -/
  genus_eq_zero : componentGenus i = 0
  /-- The diagonal entry at a `(-2)`-index is `-2` times its weight. -/
  diag_eq_neg_two_mul_weight : intersection i i = (-2 : ℤ) * weight i

namespace IsMinusTwoIndex

set_option linter.defProp false in
/-- Construct the `(-2)`-index property from its two defining equations. -/
public def ofEquations {n : ℕ} {componentGenus weight : Fin n → ℕ}
    {intersection : Matrix (Fin n) (Fin n) ℤ} {i : Fin n}
    (genus_eq_zero : componentGenus i = 0)
    (diag_eq_neg_two_mul_weight : intersection i i = (-2 : ℤ) * weight i) :
    IsMinusTwoIndex componentGenus weight intersection i :=
  ⟨genus_eq_zero, diag_eq_neg_two_mul_weight⟩

/-- The `(-2)`-index property is preserved when all numerical data are reindexed by
a permutation. -/
public theorem reindex_iff {n : ℕ} (componentGenus weight : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    IsMinusTwoIndex (componentGenus ∘ e) (weight ∘ e)
        (intersection.submatrix e e) i ↔
      IsMinusTwoIndex componentGenus weight intersection (e i) := sorry

end IsMinusTwoIndex

/-- A zero contribution of an index to the rational genus expression forces the
index to have component genus zero and diagonal intersection equal to negative
twice its weight. -/
public theorem isMinusTwoIndex_of_contribution_eq_zero (T : NumericalType) (hn : 1 < T.n)
    (i : Fin T.n)
    (hcontribution :
      (T.multiplicity i : ℚ) *
          ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
            (T.intersection i i : ℚ) / 2) = 0) :
    IsMinusTwoIndex T.componentGenus T.weight T.intersection i := sorry

end NumericalType
