/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
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
