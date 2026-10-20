/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionBounds

@[expose] public section

/- Lemma 55.7.1 (1): a positive intersection is bounded, after multiplication by its
source multiplicity, by the target multiplicity times the absolute diagonal intersection. -/
@[stacks 0C9U]
#check (NumericalType.positiveIntersectionBound :
  ∀ (T : NumericalType) (i j : Fin T.n), 0 < T.intersection i j →
    (T.multiplicity i : ℤ) * T.intersection i j ≤
      (T.multiplicity j : ℤ) * |T.intersection j j|)

/- Lemma 55.7.1 (2): when two indices have positive intersection, the source
multiplicity times its weight is bounded by the same target diagonal quantity. -/
@[stacks 0C9U]
#check (NumericalType.weightBoundOfPositiveIntersection :
  ∀ (T : NumericalType) (i j : Fin T.n), 0 < T.intersection i j →
    (T.multiplicity i : ℤ) * (T.weight i : ℤ) ≤
      (T.multiplicity j : ℤ) * |T.intersection j j|)
