/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.SourceSection

open CategoryTheory AlgebraicGeometry Limits

universe u

/- 79.5.0.1: For a groupoid in algebraic spaces `G` and source sections
`δ1`, `δ2 : G.U ⟶ G.R` with `δ1 ≫ G.s = 𝟙 G.U` and `δ2 ≫ G.s = 𝟙 G.U`,
composition is `comp G δ1 δ2 hδ1 hδ2 = G.compose (δ2 ≫ G.t ≫ δ1) δ2
(composable G δ1 δ2 hδ1)`, the Lean form of `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)`. -/
@[stacks 0CKC] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.SourceSection.comp_eq :
    ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B : AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B)
      (δ1 δ2 : G.U ⟶ G.R)
      (hδ1 : δ1 ≫ G.s = 𝟙 G.U) (hδ2 : δ2 ≫ G.s = 𝟙 G.U),
      AlgebraicGeometry.GroupoidAlgebraicSpace.SourceSection.comp G δ1 δ2 hδ1 hδ2 =
        G.compose (δ2 ≫ G.t ≫ δ1) δ2
          (AlgebraicGeometry.GroupoidAlgebraicSpace.SourceSection.composable G δ1 δ2 hδ1))
