/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Basis
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

/- Lemma 25.11.3 (01H6): every basis of a topological space admits an open hypercovering whose
indexed opens all lie in that basis. -/
@[stacks 01H6 "Lemma 25.11.3"]
#check (@SSet.OpenHypercovering.exists_degreewiseOpensIn :
  ∀ {X : Type u} [TopologicalSpace X]
    (B : Set (Opens X)) (hB : Opens.IsBasis B),
      ∃ H : SSet.OpenHypercovering.{u, u} X, H.degreewiseOpensIn B)
