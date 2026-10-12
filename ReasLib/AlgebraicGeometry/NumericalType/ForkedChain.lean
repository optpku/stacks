/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

/-- Two ordered vertices form an edge of the forked chain on `t + 1` vertices
when they are consecutive before the last vertex, or when they form the final
branch from vertex `t - 2` to vertex `t`. -/
public def IsForkEdge (t : ℕ) (r s : Fin (t + 1)) : Prop :=
  (r.val + 1 = s.val ∧ s.val < t) ∨
    (r.val + 2 = s.val ∧ s.val = t)

/-- If `4 < t` and a numerical type has more than `t + 1` indices, then
`t + 1` distinct `(-2)`-indices joined in the specified forked chain all have
the same weight. -/
public theorem forkedChainWeights (T : NumericalType) (t : ℕ) (ht : 4 < t)
    (hn : t + 1 < T.n) (v : Fin (t + 1) ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hmeet : ∀ r s, IsForkEdge t r s →
      T.intersection (v r) (v s) ≠ 0) :
    ∀ r, T.weight (v r) = T.weight (v 0) := sorry

/-- Under the same hypotheses, every edge of the specified forked chain has
intersection number equal to the common weight. -/
public theorem forkedChainEdgeIntersections (T : NumericalType) (t : ℕ) (ht : 4 < t)
    (hn : t + 1 < T.n) (v : Fin (t + 1) ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hmeet : ∀ r s, IsForkEdge t r s →
      T.intersection (v r) (v s) ≠ 0) :
    ∀ r s, IsForkEdge t r s →
      T.intersection (v r) (v s) = T.weight (v 0) := sorry

/-- Under the same hypotheses, every other lower-triangular intersection among
the specified indices is zero. -/
public theorem forkedChainOtherIntersections (T : NumericalType) (t : ℕ) (ht : 4 < t)
    (hn : t + 1 < T.n) (v : Fin (t + 1) ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hmeet : ∀ r s, IsForkEdge t r s →
      T.intersection (v r) (v s) ≠ 0) :
    ∀ r s, s < r → ¬ IsForkEdge t s r →
      T.intersection (v r) (v s) = 0 := sorry

end NumericalType
