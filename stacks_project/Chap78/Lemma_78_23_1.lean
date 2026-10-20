/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Cocycle
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open AlgebraicGeometry.GroupoidAlgebraicSpace

universe u

/- Lemma 78.23.1. Assumptions and notation as in Lemmas 78.20.2 and 78.20.3. The vertical
composition of `sourceTargetWhisker G (pullback.snd G.s G.t).left` with
`sourceTargetWhisker G (pullback.fst G.s G.t).left` equals
`sourceTargetWhisker G G.c.left`. Stacks `pr₀` is `(pullback.fst G.s G.t).left`, `pr₁` is
`(pullback.snd G.s G.t).left`, and `c` is `G.c.left`; left whiskering of `sourceTarget G` is
`CartesianBasedFunctor.precomp.map`, and vertical composition is `≫` applied to the `pr₁`
cell first and then the `pr₀` cell. -/
@[stacks 044T] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceTarget_whisker_comp :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      eqToHom (sourceTargetWhisker_source G).symm ≫
          sourceTargetWhisker G (pullback.snd G.s G.t).left ≫
          eqToHom (sourceTargetWhisker_middle G) ≫
          sourceTargetWhisker G (pullback.fst G.s G.t).left ≫
          eqToHom (sourceTargetWhisker_target G) =
        sourceTargetWhisker G G.c.left)
