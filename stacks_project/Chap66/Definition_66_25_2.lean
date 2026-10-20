/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RegularAt
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.25.2: for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, we say `X` is regular at `x` if `𝒪_{U,u}` is a regular local ring for any
(equivalently some) étale morphism `a : U → X` from a scheme with `a(u) = x`. -/
@[stacks 0AH9] #check (AlgebraicGeometry.AlgebraicSpace.RegularAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
