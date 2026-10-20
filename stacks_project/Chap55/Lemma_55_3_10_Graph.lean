/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Graph

#check (NumericalType.intersectionGraph :
  ∀ T : NumericalType, SimpleGraph (Fin T.n))
#check (NumericalType.intersectionGraph_adj :
  ∀ (T : NumericalType) (i j : Fin T.n),
    T.intersectionGraph.Adj i j ↔ i ≠ j ∧ 0 < T.intersection i j)
#check (NumericalType.intersectionGraph_connected :
  ∀ T : NumericalType, T.intersectionGraph.Connected)
#check (NumericalType.edgeCount : ∀ T : NumericalType, ℕ)
#check (NumericalType.edgeCount_eq_card_filter :
  ∀ T : NumericalType,
    T.edgeCount =
      ((Finset.univ : Finset (Fin T.n × Fin T.n)).filter fun ij ↦
        ij.1 < ij.2 ∧ 0 < T.intersection ij.1 ij.2).card)
#check (NumericalType.edgeCount_eq_card_edgeSet :
  ∀ T : NumericalType, T.edgeCount = Nat.card T.intersectionGraph.edgeSet)
