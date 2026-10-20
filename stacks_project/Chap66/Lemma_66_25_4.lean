/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Regular

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 66.25.4: a regular algebraic space is normal. -/
@[stacks 0BGT] #check (AlgebraicGeometry.AlgebraicSpace.IsRegular.instIsNormal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsRegular X],
    AlgebraicGeometry.AlgebraicSpace.IsNormal X)
