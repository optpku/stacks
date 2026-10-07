module

public import stacks_project.Chap78.Lemma_78_20_3_Comparison

/-!
# Cocycle identity for the quotient-stack atlas cell

This file records that left whiskering of the canonical `2`-morphism `sourceTarget G`
along the projections and composition of composable arrows satisfies the cocycle identity
of Lemma 78.23.1.
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
  (CartesianBasedFunctor.precomp (quotientStack G).p (stackInSets.map f)).map (sourceTarget G)

/-- `sourceTargetWhisker G f` is precomposition of `sourceTarget G` along `stackInSets.map f`. -/
theorem sourceTargetWhisker_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {X : AlgebraicSpace S} (f : X ⟶ G.R.left) :
    sourceTargetWhisker G f =
      (CartesianBasedFunctor.precomp (quotientStack G).p (stackInSets.map f)).map
        (sourceTarget G) :=
  sorry

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

/-- Lemma 78.23.1. Assumptions and notation as in Lemmas 78.20.2 and 78.20.3. The vertical
composition of `sourceTargetWhisker G (pullback.snd G.s G.t).left` with
`sourceTargetWhisker G (pullback.fst G.s G.t).left` equals
`sourceTargetWhisker G G.c.left`. Stacks `pr₀` is `(pullback.fst G.s G.t).left`, `pr₁` is
`(pullback.snd G.s G.t).left`, and `c` is `G.c.left`; left whiskering of `sourceTarget G` is
`CartesianBasedFunctor.precomp.map`, and vertical composition is `≫` applied to the `pr₁`
cell first and then the `pr₀` cell. -/
@[stacks 044T]
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

