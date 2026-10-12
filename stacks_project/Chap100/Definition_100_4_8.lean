/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_4_7_Topology
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicStack

/- Definition 100.4.8: let `X` be an algebraic stack. The underlying topological
space of `X` is the set of points `|X|` endowed with the topology constructed in
Lemma 100.4.7. -/
@[stacks 04Y8] #check
  (AlgebraicGeometry.AlgebraicStack.instTopologicalSpacePoints :
    {S : Scheme.{u}} → (X : GroupoidsOver S) → [AlgebraicStack X] →
      TopologicalSpace (Points X))
