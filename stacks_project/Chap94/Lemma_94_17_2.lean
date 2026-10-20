/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Smooth
import StacksCheckRecall

/-!
# Smooth surjective atlas of a quotient stack

The atlas 1-morphism `𝒮_U ⟶ [U / R]` of a smooth groupoid in algebraic spaces
is a smooth surjective 1-morphism of categories fibred in groupoids.
-/

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 94.17.2: let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a smooth groupoid in algebraic spaces over `S`. Then the
morphism `𝒮_U ⟶ [U / R]` is smooth and surjective. Formalized for a smooth groupoid `G` in
algebraic spaces over an algebraic space `B` over `S`, with `𝒮_U` as
`G.U.left.toGroupoids`, `[U / R]` as `SmallQuotient.quotientStack G`, and the morphism as
`SmallQuotient.atlas G`. -/
@[stacks 04X0] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.smooth_surjective_atlas :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      GroupoidAlgebraicSpace.Smooth G →
        Groupoids.Hom.Smooth
            (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.atlas G) ∧
          Groupoids.Hom.Surjective
            (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.atlas G))
