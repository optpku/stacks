/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.OneIndex

@[expose] public section

/- Lemma 55.3.5 (1): a numerical type with one index has zero diagonal intersection. -/
@[stacks 0C73] #check (NumericalType.oneIndex_intersection_self_eq_zero :
    (T : NumericalType) → T.n = 1 → (i : Fin T.n) → T.intersection i i = 0)

/- Lemma 55.3.5 (2): for one index, the genus has the stated multiplicity-weighted expression. -/
@[stacks 0C73] #check (NumericalType.oneIndex_genus_eq :
    (T : NumericalType) → T.n = 1 → (i : Fin T.n) →
      T.genus = 1 + (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
        ((T.componentGenus i : ℤ) - 1))

/- Lemma 55.3.5 (3): negative genus gives component genus zero and the displayed factorization. -/
@[stacks 0C73] #check (NumericalType.oneIndex_negative_classification :
    (T : NumericalType) → T.n = 1 → (g : ℤ) → T.genus = g → g < 0 →
      (i : Fin T.n) →
      T.componentGenus i = 0 ∧
        (T.multiplicity i : ℤ) * (T.weight i : ℤ) = 1 - g)

/- Lemma 55.3.5 (4): one-index numerical types of a fixed negative genus are finite. -/
@[stacks 0C73] #check (NumericalType.oneIndex_negative_finite :
    (g : ℤ) → g < 0 → Set.Finite {T : NumericalType | T.n = 1 ∧ T.genus = g})

/- Lemma 55.3.5 (5): genus zero forces one-index multiplicity one. -/
@[stacks 0C73] #check (NumericalType.oneIndex_zero_multiplicity :
    (T : NumericalType) → T.n = 1 → T.genus = 0 → (i : Fin T.n) →
      T.multiplicity i = 1)

/- Lemma 55.3.5 (6): genus zero forces one-index weight one. -/
@[stacks 0C73] #check (NumericalType.oneIndex_zero_weight :
    (T : NumericalType) → T.n = 1 → T.genus = 0 → (i : Fin T.n) →
      T.weight i = 1)

/- Lemma 55.3.5 (7): genus zero forces one-index component genus zero. -/
@[stacks 0C73] #check (NumericalType.oneIndex_zero_componentGenus :
    (T : NumericalType) → T.n = 1 → T.genus = 0 → (i : Fin T.n) →
      T.componentGenus i = 0)

/- Lemma 55.3.5 (8): genus one forces the sole component genus to be one. -/
@[stacks 0C73] #check (NumericalType.oneIndex_one_componentGenus :
    (T : NumericalType) → T.n = 1 → T.genus = 1 → (i : Fin T.n) →
      T.componentGenus i = 1)

/- Lemma 55.3.5 (9): genus greater than one gives the displayed component genus and factorization. -/
@[stacks 0C73] #check (NumericalType.oneIndex_positive_classification :
    (T : NumericalType) → T.n = 1 → (g : ℤ) → T.genus = g → 1 < g →
      (i : Fin T.n) →
      1 < T.componentGenus i ∧
        (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
            ((T.componentGenus i : ℤ) - 1) = g - 1)

/- Lemma 55.3.5 (10): one-index numerical types of a fixed genus greater than one are finite. -/
@[stacks 0C73] #check (NumericalType.oneIndex_positive_finite :
    (g : ℤ) → 1 < g → Set.Finite {T : NumericalType | T.n = 1 ∧ T.genus = g})

/- The one-index constructor is available with its defining positivity hypotheses. -/
#check (NumericalType.oneIndex :
    (multiplicity weight componentGenus : ℕ) → 0 < multiplicity → 0 < weight → NumericalType)

/- The one-index constructor has the expected genus formula. -/
#check (NumericalType.genus_oneIndex :
    (multiplicity weight componentGenus : ℕ) → (hm : 0 < multiplicity) → (hw : 0 < weight) →
      (NumericalType.oneIndex multiplicity weight componentGenus hm hw).genus =
        1 + (multiplicity : ℤ) * (weight : ℤ) * ((componentGenus : ℤ) - 1))

/- The one-index constructor has the expected equality characterization. -/
#check (NumericalType.eq_oneIndex_iff :
    (T : NumericalType) → (multiplicity weight componentGenus : ℕ) →
      (hm : 0 < multiplicity) → (hw : 0 < weight) →
      T = NumericalType.oneIndex multiplicity weight componentGenus hm hw ↔
        T.n = 1 ∧ ∀ i : Fin T.n,
          T.multiplicity i = multiplicity ∧ T.weight i = weight ∧
            T.componentGenus i = componentGenus)
