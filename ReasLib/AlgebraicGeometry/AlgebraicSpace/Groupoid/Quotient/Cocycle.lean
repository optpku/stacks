/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Comparison
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition

/-!
# Cocycle identity for the quotient-stack atlas cell

The canonical atlas cell of a quotient stack can be whiskered along morphisms of algebraic
spaces. Its whiskerings along the projections of composable arrows satisfy the cocycle
identity, after identifying their source, middle, and target endpoints.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Left whiskering of the canonical atlas cell `sourceTarget G` by the cartesian `1`-morphism
associated to a morphism `f : X ⟶ G.R.left`. -/
def sourceTargetWhisker {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : AlgebraicSpace S} (f : X ⟶ G.R.left) :
    (stackInSets.map f).comp (atlasSource G) ⟶ (stackInSets.map f).comp (atlasTarget G) :=
  (CartesianBasedFunctor.precomp (fppfQuotientStack G).p (stackInSets.map f)).map (sourceTarget G)

/-- `sourceTargetWhisker G f` is precomposition of `sourceTarget G` along `stackInSets.map f`. -/
theorem sourceTargetWhisker_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : AlgebraicSpace S} (f : X ⟶ G.R.left) :
    sourceTargetWhisker G f =
      (CartesianBasedFunctor.precomp (fppfQuotientStack G).p (stackInSets.map f)).map
        (sourceTarget G) :=
  rfl

/-- The composites `π ∘ s ∘ pr₁` and `π ∘ s ∘ c` agree as cartesian `1`-morphisms, where
`pr₁` is `(pullback.snd G.s G.t).left` and `c` is `G.c.left`. -/
theorem sourceTargetWhisker_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSets.map (pullback.snd G.s G.t).left).comp (atlasSource G) =
      (stackInSets.map G.c.left).comp (atlasSource G) :=
  sorry

/-- The composites `π ∘ t ∘ pr₁` and `π ∘ s ∘ pr₀` agree as cartesian `1`-morphisms, where
`pr₀` is `(pullback.fst G.s G.t).left` and `pr₁` is `(pullback.snd G.s G.t).left`. -/
theorem sourceTargetWhisker_middle {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSets.map (pullback.snd G.s G.t).left).comp (atlasTarget G) =
      (stackInSets.map (pullback.fst G.s G.t).left).comp (atlasSource G) :=
  sorry

/-- The composites `π ∘ t ∘ pr₀` and `π ∘ t ∘ c` agree as cartesian `1`-morphisms, where
`pr₀` is `(pullback.fst G.s G.t).left` and `c` is `G.c.left`. -/
theorem sourceTargetWhisker_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSets.map (pullback.fst G.s G.t).left).comp (atlasTarget G) =
      (stackInSets.map G.c.left).comp (atlasTarget G) :=
  sorry

/-- The canonical quotient-atlas cell whiskered along groupoid composition equals the
vertical composite of its whiskerings along the second and then the first pullback projection,
transported through the canonical endpoint equalities. -/
theorem sourceTarget_whisker_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    eqToHom (sourceTargetWhisker_source G).symm ≫
        sourceTargetWhisker G (pullback.snd G.s G.t).left ≫
        eqToHom (sourceTargetWhisker_middle G) ≫
        sourceTargetWhisker G (pullback.fst G.s G.t).left ≫
        eqToHom (sourceTargetWhisker_target G) =
      sourceTargetWhisker G G.c.left :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

