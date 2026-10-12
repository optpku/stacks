/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

/-- The simple graph whose edges are the positive off-diagonal intersections of a numerical type. -/
public def intersectionGraph (T : NumericalType) : SimpleGraph (Fin T.n) :=
  SimpleGraph.fromRel fun i j ↦ 0 < T.intersection i j

/-- Two indices are adjacent in `intersectionGraph` exactly when they are distinct and their intersection is positive. -/
public theorem intersectionGraph_adj (T : NumericalType) (i j : Fin T.n) :
    T.intersectionGraph.Adj i j ↔ i ≠ j ∧ 0 < T.intersection i j := sorry

/-- The positive-intersection graph of a numerical type is connected. -/
public theorem intersectionGraph_connected (T : NumericalType) :
    T.intersectionGraph.Connected := sorry

/-- The number of pairs `i < j` with positive intersection in a numerical type. -/
public def edgeCount (T : NumericalType) : ℕ :=
  ((Finset.univ : Finset (Fin T.n × Fin T.n)).filter fun ij ↦
    ij.1 < ij.2 ∧ 0 < T.intersection ij.1 ij.2).card

/-- `edgeCount` is the cardinality of the filtered set of pairs `i < j` with positive intersection. -/
public theorem edgeCount_eq_card_filter (T : NumericalType) :
    T.edgeCount =
      ((Finset.univ : Finset (Fin T.n × Fin T.n)).filter fun ij ↦
        ij.1 < ij.2 ∧ 0 < T.intersection ij.1 ij.2).card := sorry

/-- `edgeCount` is the cardinality of the edge set of `intersectionGraph`. -/
public theorem edgeCount_eq_card_edgeSet (T : NumericalType) :
    T.edgeCount = Nat.card T.intersectionGraph.edgeSet := sorry

/-- The number of indices of a numerical type is at most one more than its number of positive off-diagonal intersections. -/
public theorem n_le_edgeCount_add_one (T : NumericalType) :
    T.n ≤ T.edgeCount + 1 := sorry

/-- The integer expression `1 - T.n + T.edgeCount` associated to a numerical type is nonnegative. -/
public theorem topologicalGenusExpression_nonnegative (T : NumericalType) :
    0 ≤ (1 : ℤ) - T.n + T.edgeCount := sorry

/-- In a numerical type with more than five indices, five distinct `(-2)`-indices
cannot have positive intersection between one central index and each of the other four. -/
public theorem noFourMinusTwoNeighbors (T : NumericalType) (hn : 5 < T.n)
    (v : Fin 5 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hhi : 0 < T.intersection (v 0) (v 1))
    (hhj : 0 < T.intersection (v 0) (v 2))
    (hhk : 0 < T.intersection (v 0) (v 3))
    (hhl : 0 < T.intersection (v 0) (v 4)) : False := sorry

/-- In a numerical type with more than seven indices, seven distinct `(-2)`-indices
cannot form three length-two arms with nonzero intersections meeting at a common center. -/
public theorem noThreeArmedMinusTwoSubgraph (T : NumericalType) (hn : 7 < T.n)
    (v : Fin 7 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hfg : T.intersection (v 0) (v 1) ≠ 0)
    (hgh : T.intersection (v 1) (v 2) ≠ 0)
    (hij : T.intersection (v 3) (v 4) ≠ 0)
    (hjh : T.intersection (v 4) (v 2) ≠ 0)
    (hkl : T.intersection (v 5) (v 6) ≠ 0)
    (hlh : T.intersection (v 6) (v 2) ≠ 0) : False := sorry

/-- In a numerical type with more than eight indices, eight distinct `(-2)`-indices
cannot form a seven-edge chain with one additional edge from the last index to
the fourth index. -/
public theorem noForkedSevenChainMinusTwoSubgraph (T : NumericalType) (hn : 8 < T.n)
    (v : Fin 8 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hef : T.intersection (v 0) (v 1) ≠ 0)
    (hfg : T.intersection (v 1) (v 2) ≠ 0)
    (hgh : T.intersection (v 2) (v 3) ≠ 0)
    (hhi : T.intersection (v 3) (v 4) ≠ 0)
    (hij : T.intersection (v 4) (v 5) ≠ 0)
    (hjk : T.intersection (v 5) (v 6) ≠ 0)
    (hlh : T.intersection (v 7) (v 3) ≠ 0) : False := sorry

/-- In a numerical type with more than nine indices, nine distinct `(-2)`-indices
cannot form a chain from positions `0` through `7` with nonzero intersections,
together with a nonzero intersection between positions `8` and `4`. -/
public theorem noForkedEightChainMinusTwoSubgraph (T : NumericalType) (hn : 9 < T.n)
    (v : Fin 9 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hde : T.intersection (v 0) (v 1) ≠ 0)
    (hef : T.intersection (v 1) (v 2) ≠ 0)
    (hfg : T.intersection (v 2) (v 3) ≠ 0)
    (hgh : T.intersection (v 3) (v 4) ≠ 0)
    (hhi : T.intersection (v 4) (v 5) ≠ 0)
    (hij : T.intersection (v 5) (v 6) ≠ 0)
    (hjk : T.intersection (v 6) (v 7) ≠ 0)
    (hlh : T.intersection (v 8) (v 4) ≠ 0) : False := sorry

/-- For `4 ≤ t` and `t + 2 < T.n`, no `t + 2` distinct `(-2)`-indices can have
positive intersections along the chain from positions `1` through `t`, together
with positive intersections between positions `0` and `2`, and positions
`t - 1` and `t + 1`. -/
public theorem noDoubleForkMinusTwoSubgraph (T : NumericalType) (t : ℕ) (ht : 4 ≤ t)
    (hn : t + 2 < T.n) (v : Fin (t + 2) ↪ Fin T.n)
    (hminusTwo : ∀ r,
      IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (hchain : ∀ r s, 1 ≤ r.val → r.val + 1 = s.val → s.val ≤ t →
      0 < T.intersection (v r) (v s))
    (hleft : ∀ r s, r.val = 0 → s.val = 2 →
      0 < T.intersection (v r) (v s))
    (hright : ∀ r s, r.val + 1 = t → s.val = t + 1 →
      0 < T.intersection (v r) (v s)) : False := sorry

end NumericalType
