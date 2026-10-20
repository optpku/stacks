/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 33.43.1: Let `k` be a field. A curve is a variety of dimension `1` over `k`. -/
@[stacks 0A23] #check
  (@AlgebraicGeometry.curve_iff :
    ∀ {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))),
      AlgebraicGeometry.Curve X ↔
        AlgebraicGeometry.Variety X ∧ topologicalKrullDim X.left = 1)
