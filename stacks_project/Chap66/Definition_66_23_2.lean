/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranch
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.23.2 (1): for a scheme `S`, an algebraic space `X` over `S`, and a point
`x ∈ |X|`, we say `X` is geometrically unibranch at `x` if the equivalent conditions of
Lemma 66.23.1 hold. -/
@[stacks 06DL] #check (AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranchAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)

/- Definition 66.23.2 (2): we say that `X` is geometrically unibranch if `X` is
geometrically unibranch at every `x ∈ |X|`. -/
@[stacks 06DL] #check (AlgebraicGeometry.AlgebraicSpace.IsGeometricallyUnibranch :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
