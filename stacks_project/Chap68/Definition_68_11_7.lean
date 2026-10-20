/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
import StacksCheckRecall

universe u

/- Definition 68.11.7: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|`. The henselian local ring of `X` at `x` is
`henselianLocalRing X x = colim Γ(U, 𝒪_U)`, where the colimit is over the elementary
étale neighbourhoods `(U, u) ⟶ (X, x)`. -/
@[stacks 0BGW] #check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X), Type (u + 1))
