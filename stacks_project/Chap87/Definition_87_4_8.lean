/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 87.4.8 (1): an element `f` of a linearly topologized ring is
topologically nilpotent if `f ^ n` tends to `0` as `n` tends to infinity. -/
@[stacks 0AMV] #check (TopologicalRing.IsTopologicallyNilpotent :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R], R → Prop)

/- Definition 87.4.8 (2): a weak ideal of definition is an open ideal consisting
entirely of topologically nilpotent elements. -/
@[stacks 0AMV] #check (TopologicalRing.Ideal.IsWeakIdealOfDefinition :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R], Ideal R → Prop)

/- Definition 87.4.8 (3): a linearly topologized ring is weakly pre-admissible if it
has a weak ideal of definition. -/
@[stacks 0AMV] #check (TopologicalRing.IsWeaklyPreadmissibleRing :
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R], Prop)

/- Definition 87.4.8 (4): a linearly topologized ring is weakly admissible if it is
weakly pre-admissible and complete, including separated. -/
@[stacks 0AMV] #check (TopologicalRing.IsWeaklyAdmissibleRing :
  ∀ (R : Type u) [CommRing R] [TopologicalSpace R], Prop)
