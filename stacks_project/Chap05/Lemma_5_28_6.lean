/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Stratification.Refinement
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 5.28.6: finite locally closed partitions admit finite stratification refinements. -/
@[stacks 09Y3]
#check (LocallyClosedPartition.exists_finite_stratification_refining :
  ∀ {X : Type u} [TopologicalSpace X] (P : LocallyClosedPartition X),
    P.toSet.Finite →
      ∃ S : FiniteStratification.{u, 0} X, S.toLocallyClosedPartition.Refines P)

/- A produced refinement exposes its finite index, order, family, and stratification proof through
one reusable data owner. -/
#check FiniteStratification
#check FiniteStratification.ofStrata
#check FiniteStratification.toLocallyClosedPartition
#check fun {X : Type} [TopologicalSpace X] (S : FiniteStratification X) ↦
  S.instFinite
#check fun {X : Type} [TopologicalSpace X] (S : FiniteStratification X) ↦
  S.instPartialOrder
