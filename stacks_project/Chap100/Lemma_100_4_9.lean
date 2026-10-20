/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.LocallyCompact

/-!
# Local quasi-compactness of algebraic stacks

Every point of `|X|` has a fundamental system of quasi-compact open neighbourhoods.
In particular `|X|` is locally quasi-compact in the sense of Topology, Definition 5.13.1.
-/

@[expose] public section

universe u

/- Lemma 100.4.9. Every point of an algebraic stack has a fundamental system of
quasi-compact open neighbourhoods. In particular, its point space is locally
quasi-compact, by the generic instance for prespectral spaces. -/
@[stacks 04Y9] #check
  (AlgebraicGeometry.AlgebraicStack.instPrespectralSpacePoints :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
      [AlgebraicGeometry.AlgebraicStack X],
      PrespectralSpace (AlgebraicGeometry.AlgebraicStack.Points X))
