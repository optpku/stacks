/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.InvariantBounds

@[expose] public section

/- Lemma 55.7.2 -/
@[stacks 0C9V]
#check (NumericalType.nonMinusTwoIndexCardBound : ∀ (g : ℤ), 2 ≤ g →
    ∀ (T : NumericalType), T.genus = g → T.IsMinimal → 1 < T.n →
    (Set.ncard {j : Fin T.n |
      ¬ NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection j} : ℤ) ≤
      2 * g - 2)

#check (NumericalType.componentGenusBoundOfNotMinusTwo : ∀ (g : ℤ), 2 ≤ g →
    ∀ (T : NumericalType), T.genus = g → T.IsMinimal → 1 < T.n → ∀ (j : Fin T.n),
    ¬ NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection j →
    (T.componentGenus j : ℤ) < g)

#check (NumericalType.diagonalBoundOfNotMinusTwo : ∀ (g : ℤ), 2 ≤ g →
    ∀ (T : NumericalType), T.genus = g → T.IsMinimal → 1 < T.n → ∀ (j : Fin T.n),
    ¬ NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection j →
    (T.multiplicity j : ℤ) * |T.intersection j j| ≤ 6 * g - 6)

#check (NumericalType.intersectionBoundOfNotMinusTwo : ∀ (g : ℤ), 2 ≤ g →
    ∀ (T : NumericalType), T.genus = g → T.IsMinimal → 1 < T.n → ∀ (j : Fin T.n),
    ¬ NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection j →
    ∀ (i : Fin T.n), (T.multiplicity i : ℤ) * T.intersection i j ≤ 6 * g - 6)
