module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicSpace

/- Definition 66.4.7: let `S` be a scheme. Let `X` be an algebraic space over `S`.
The underlying topological space of `X` is the set of points `|X|` endowed with
the topology constructed in Lemma 66.4.6. -/
@[stacks 03BY] #check
  (AlgebraicGeometry.AlgebraicSpace.instTopologicalSpacePoints :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) → TopologicalSpace (Points X))
