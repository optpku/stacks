module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.LocallyCompact
import StacksCheckRecall

universe u

/- Lemma 66.5.5. Let `S` be a scheme and `X` an algebraic space over `S`.
Every point of `|X|` has a fundamental system of open quasi-compact neighbourhoods.
In particular `|X|` is locally quasi-compact in the sense of Topology, Definition 5.13.1. -/
@[stacks 04NN] #check (AlgebraicGeometry.AlgebraicSpace.Points.prespectralSpace :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    PrespectralSpace (AlgebraicGeometry.AlgebraicSpace.Points X))
