/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Jacobson.Basic
import StacksCheckRecall

@[expose] public section

/- Lemma 5.18.2: density of closed points in every singleton closure implies
that the space is Jacobson. -/
@[stacks 005V]
#check fun {X : Type*} [TopologicalSpace X]
    (hDense : ∀ x : X,
      closure (closure ({x} : Set X) ∩ closedPoints X) = closure ({x} : Set X)) ↦
  jacobsonSpace_iff_dense_closedPoints_in_singleton_closure.mpr hDense
