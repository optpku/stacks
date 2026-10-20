/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfGroup
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

variable {S : Scheme.{u}} {k : Type u} [Field k]
  (σ : Spec (CommRingCat.of k) ⟶ S)

/- 79.9.2.1: In Situation 79.9.1, with `S` a scheme, `k` a field over `S` via
`σ : Spec (CommRingCat.of k) ⟶ S`, and `G` a group algebraic space over
`Spec k`, the group determines the groupoid in algebraic spaces
`(Spec k, G, p, p, m)`, where `p = toUnit G.X` is the structure morphism of `G`
and `m = μ[G.X]` is the group law. This is `GroupoidAlgebraicSpace.ofGroup G`
at `B = AlgebraicSpace.ofOver (Over.mk σ)`, so the object space is the tensor
unit `𝟙_ (Over B)` (identified with `Spec k`) and the arrow space is `G`. -/
@[stacks 06DZ] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.ofGroup :
    GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)) →
      GroupoidAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
