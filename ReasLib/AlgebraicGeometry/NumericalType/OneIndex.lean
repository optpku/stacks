/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Genus

open scoped BigOperators

namespace NumericalType

/-- A numerical type with one index and constant multiplicity, weight, and component genus. -/
public def oneIndex (multiplicity weight componentGenus : ℕ) (hm : 0 < multiplicity)
    (hw : 0 < weight) : NumericalType :=
  NumericalType.of 1 Nat.zero_lt_one (fun _ => multiplicity) (fun _ => weight)
    (fun _ => componentGenus) (fun _ _ => 0) (fun _ => hm) (fun _ => hw)
    (fun _ _ => rfl) (fun _ _ _ => le_rfl)
    (fun I hI hI_univ => False.elim (hI_univ (Set.Nonempty.eq_univ hI)))
    (fun _ => Finset.sum_eq_zero (fun j hj => zero_mul (multiplicity : ℤ)))
    (fun _ _ => dvd_zero _)

/-- The diagonal intersection of a one-index numerical type is zero. -/
public theorem oneIndex_intersection_self_eq_zero
    (T : NumericalType) (h_n : T.n = 1) (i : Fin T.n) :
    T.intersection i i = 0 := sorry

/-- The genus of a one-index numerical type is its multiplicity-weighted component-genus expression. -/
public theorem oneIndex_genus_eq
    (T : NumericalType) (h_n : T.n = 1) (i : Fin T.n) :
    T.genus =
      1 + (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
        ((T.componentGenus i : ℤ) - 1) := sorry

/-- A negative-genus one-index numerical type has component genus zero and the corresponding factorization. -/
public theorem oneIndex_negative_classification
    (T : NumericalType) (h_n : T.n = 1) (g : ℤ) (hgenus : T.genus = g)
    (hg : g < 0) (i : Fin T.n) :
    T.componentGenus i = 0 ∧
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) = 1 - g := sorry

/-- For a fixed negative genus, the one-index numerical types form a finite set. -/
public theorem oneIndex_negative_finite (g : ℤ) (hg : g < 0) :
    Set.Finite {T : NumericalType | T.n = 1 ∧ T.genus = g} := sorry

/-- A genus-zero one-index numerical type has multiplicity one. -/
public theorem oneIndex_zero_multiplicity
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 0)
    (i : Fin T.n) :
    T.multiplicity i = 1 := sorry

/-- A genus-zero one-index numerical type has weight one. -/
public theorem oneIndex_zero_weight
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 0)
    (i : Fin T.n) :
    T.weight i = 1 := sorry

/-- A genus-zero one-index numerical type has component genus zero. -/
public theorem oneIndex_zero_componentGenus
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 0)
    (i : Fin T.n) :
    T.componentGenus i = 0 := sorry

/-- A genus-one one-index numerical type has component genus one. -/
public theorem oneIndex_one_componentGenus
    (T : NumericalType) (h_n : T.n = 1) (hgenus : T.genus = 1)
    (i : Fin T.n) :
    T.componentGenus i = 1 := sorry

/-- A one-index numerical type of genus greater than one has component genus greater than one and the corresponding factorization. -/
public theorem oneIndex_positive_classification
    (T : NumericalType) (h_n : T.n = 1) (g : ℤ) (hgenus : T.genus = g)
    (hg : 1 < g) (i : Fin T.n) :
    1 < T.componentGenus i ∧
      (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) = g - 1 := sorry

/-- For a fixed genus greater than one, the one-index numerical types form a finite set. -/
public theorem oneIndex_positive_finite (g : ℤ) (hg : 1 < g) :
    Set.Finite {T : NumericalType | T.n = 1 ∧ T.genus = g} := sorry

/-- The genus of the canonical one-index numerical type is the prescribed factorization expression. -/
public theorem genus_oneIndex (multiplicity weight componentGenus : ℕ) (hm : 0 < multiplicity)
    (hw : 0 < weight) :
    (oneIndex multiplicity weight componentGenus hm hw).genus =
      1 + (multiplicity : ℤ) * (weight : ℤ) * ((componentGenus : ℤ) - 1) := sorry

/-- Equality with a canonical one-index numerical type is characterized by its indexed data. -/
public theorem eq_oneIndex_iff (T : NumericalType) (multiplicity weight componentGenus : ℕ)
    (hm : 0 < multiplicity) (hw : 0 < weight) :
    T = oneIndex multiplicity weight componentGenus hm hw ↔
      T.n = 1 ∧ ∀ i : Fin T.n,
        T.multiplicity i = multiplicity ∧ T.weight i = weight ∧
          T.componentGenus i = componentGenus := sorry

end NumericalType
