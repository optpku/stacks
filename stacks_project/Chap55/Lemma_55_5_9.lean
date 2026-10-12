/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedChain

/- Lemma 55.5.9: if `4 < t` and a numerical type has more than `t + 1`
indices, then `t + 1` distinct `(-2)`-indices joined in the specified forked
chain have one common weight, edge intersections equal to that weight, and all
other lower-triangular intersections zero. -/
@[stacks 0C8D] #check (NumericalType.forkedChainWeights :
  ∀ (T : NumericalType) (t : ℕ), 4 < t → t + 1 < T.n →
    (v : Fin (t + 1) ↪ Fin T.n) →
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight
      T.intersection (v r)) →
    (∀ r s, NumericalType.IsForkEdge t r s →
      T.intersection (v r) (v s) ≠ 0) →
    ∀ r, T.weight (v r) = T.weight (v 0))

#check (NumericalType.forkedChainEdgeIntersections :
  ∀ (T : NumericalType) (t : ℕ), 4 < t → t + 1 < T.n →
    (v : Fin (t + 1) ↪ Fin T.n) →
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight
      T.intersection (v r)) →
    (∀ r s, NumericalType.IsForkEdge t r s →
      T.intersection (v r) (v s) ≠ 0) →
    ∀ r s, NumericalType.IsForkEdge t r s →
      T.intersection (v r) (v s) = T.weight (v 0))

#check (NumericalType.forkedChainOtherIntersections :
  ∀ (T : NumericalType) (t : ℕ), 4 < t → t + 1 < T.n →
    (v : Fin (t + 1) ↪ Fin T.n) →
    (∀ r, NumericalType.IsMinusTwoIndex T.componentGenus T.weight
      T.intersection (v r)) →
    (∀ r s, NumericalType.IsForkEdge t r s →
      T.intersection (v r) (v s) ≠ 0) →
    ∀ r s, s < r → ¬ NumericalType.IsForkEdge t s r →
      T.intersection (v r) (v s) = 0)
