/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap78.Lemma_78_15_1_Action
import StacksCheckRecall

universe u

open AlgebraicGeometry

/- Lemma 78.15.1: a group algebraic space `G` over `B` acting on an algebraic space
`X` over `B` determines a groupoid in algebraic spaces over `B` with `U = X`,
`R = G ×_B X`, source `(g, x) ↦ x`, target `(g, x) ↦ a(g, x)`, composition
`((g, x), (g', x')) ↦ (m(g, g'), x')`, identity `x ↦ (e_G(x), x)`, and inverse
`(g, x) ↦ (i_G(g), a(g, x))`. -/
@[stacks 0444] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.ofAction :
    {S : Scheme.{u}} → {B : AlgebraicSpace S} → (G : GroupAlgebraicSpace B) →
      GroupAlgebraicSpace.Action G → GroupoidAlgebraicSpace B)
