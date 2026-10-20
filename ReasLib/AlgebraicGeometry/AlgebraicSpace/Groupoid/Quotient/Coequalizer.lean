module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Comparison
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition

/-!
# Weak 2-coequalizer property of a quotient stack

This module records the cocycle identity on a general 2-arrow `β : f ∘ s ⟶ f ∘ t` and the
factorization of such data through the quotient stack `[U/R]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u uX vX

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The composites `f ∘ s ∘ pr₁` and `f ∘ s ∘ c` agree as cartesian 1-morphisms, where `pr₁`
is `(pullback.snd G.s G.t).left` and `c` is `G.c.left`. -/
theorem compWhisker_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p) :
    (stackInSets.map (pullback.snd G.s G.t).left).comp
        ((stackInSets.map G.s.left).comp f) =
      (stackInSets.map G.c.left).comp ((stackInSets.map G.s.left).comp f) :=
  sorry

/-- The composites `f ∘ t ∘ pr₁` and `f ∘ s ∘ pr₀` agree as cartesian 1-morphisms, where
`pr₀` is `(pullback.fst G.s G.t).left` and `pr₁` is `(pullback.snd G.s G.t).left`. -/
theorem compWhisker_middle {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p) :
    (stackInSets.map (pullback.snd G.s G.t).left).comp
        ((stackInSets.map G.t.left).comp f) =
      (stackInSets.map (pullback.fst G.s G.t).left).comp
        ((stackInSets.map G.s.left).comp f) :=
  sorry

/-- The composites `f ∘ t ∘ pr₀` and `f ∘ t ∘ c` agree as cartesian 1-morphisms, where `pr₀`
is `(pullback.fst G.s G.t).left` and `c` is `G.c.left`. -/
theorem compWhisker_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p) :
    (stackInSets.map (pullback.fst G.s G.t).left).comp
        ((stackInSets.map G.t.left).comp f) =
      (stackInSets.map G.c.left).comp ((stackInSets.map G.t.left).comp f) :=
  sorry

/-- The cocycle identity `β ★ id_c = (β ★ id_pr₀) ∘ (β ★ id_pr₁)` on a 2-arrow
`β : f ∘ s ⟶ f ∘ t`, written in diagrammatic order with `pr₁` first. -/
def IsCoequalizerCocycle {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f) : Prop :=
  eqToHom (compWhisker_source G f).symm ≫
      (CartesianBasedFunctor.precomp X.p (stackInSets.map (pullback.snd G.s G.t).left)).map β ≫
      eqToHom (compWhisker_middle G f) ≫
      (CartesianBasedFunctor.precomp X.p (stackInSets.map (pullback.fst G.s G.t).left)).map β ≫
      eqToHom (compWhisker_target G f) =
    (CartesianBasedFunctor.precomp X.p (stackInSets.map G.c.left)).map β

/-- Unfolding of `IsCoequalizerCocycle` as the whisker identity on `β`. -/
theorem IsCoequalizerCocycle.eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hβ : IsCoequalizerCocycle G f β) :
    eqToHom (compWhisker_source G f).symm ≫
        (CartesianBasedFunctor.precomp X.p (stackInSets.map (pullback.snd G.s G.t).left)).map β ≫
        eqToHom (compWhisker_middle G f) ≫
        (CartesianBasedFunctor.precomp X.p (stackInSets.map (pullback.fst G.s G.t).left)).map β ≫
        eqToHom (compWhisker_target G f) =
      (CartesianBasedFunctor.precomp X.p (stackInSets.map G.c.left)).map β :=
  hβ

/-- `IsCoequalizerCocycle` is equivalent to the whisker identity on `β`. -/
theorem IsCoequalizerCocycle.iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f) :
    IsCoequalizerCocycle G f β ↔
      eqToHom (compWhisker_source G f).symm ≫
          (CartesianBasedFunctor.precomp X.p (stackInSets.map (pullback.snd G.s G.t).left)).map β ≫
          eqToHom (compWhisker_middle G f) ≫
          (CartesianBasedFunctor.precomp X.p (stackInSets.map (pullback.fst G.s G.t).left)).map β ≫
          eqToHom (compWhisker_target G f) =
        (CartesianBasedFunctor.precomp X.p (stackInSets.map G.c.left)).map β :=
  Iff.rfl

/-- Associativity identifying `(π ∘ s) ∘ g` with `s` then `π ∘ g`. -/
theorem atlasSource_comp_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (hom : CartesianBasedFunctor (fppfQuotientStack G).p X.p) :
    (atlasSource G).comp hom =
      (stackInSets.map G.s.left).comp ((fppfAtlas G).comp hom) :=
  sorry

/-- Associativity identifying `(π ∘ t) ∘ g` with `t` then `π ∘ g`. -/
theorem atlasTarget_comp_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (hom : CartesianBasedFunctor (fppfQuotientStack G).p X.p) :
    (atlasTarget G).comp hom =
      (stackInSets.map G.t.left).comp ((fppfAtlas G).comp hom) :=
  sorry

/-- Compatibility of `g ★ α` with `β` after transporting along a triangle 2-isomorphism. -/
def IsCoequalizerCompat {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hom : CartesianBasedFunctor (fppfQuotientStack G).p X.p)
    (triangle : (fppfAtlas G).comp hom ≅ f) : Prop :=
  eqToHom (atlasSource_comp_hom G hom) ≫
      (CartesianBasedFunctor.precomp X.p (stackInSets.map G.s.left)).map triangle.hom ≫
      β =
    (CartesianBasedFunctor.postcomp (stackInSets G.R.left).p hom).map (sourceTarget G) ≫
      eqToHom (atlasTarget_comp_hom G hom) ≫
        (CartesianBasedFunctor.precomp X.p (stackInSets.map G.t.left)).map triangle.hom

/-- Unfolding of `IsCoequalizerCompat` as an equality of 2-arrows. -/
theorem IsCoequalizerCompat.eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hom : CartesianBasedFunctor (fppfQuotientStack G).p X.p)
    (triangle : (fppfAtlas G).comp hom ≅ f)
    (h : IsCoequalizerCompat G f β hom triangle) :
    eqToHom (atlasSource_comp_hom G hom) ≫
        (CartesianBasedFunctor.precomp X.p (stackInSets.map G.s.left)).map triangle.hom ≫
        β =
      (CartesianBasedFunctor.postcomp (stackInSets G.R.left).p hom).map (sourceTarget G) ≫
        eqToHom (atlasTarget_comp_hom G hom) ≫
          (CartesianBasedFunctor.precomp X.p (stackInSets.map G.t.left)).map triangle.hom :=
  h

/-- A cartesian morphism from the object-space stack with a cocycle 2-arrow factors through
the fppf quotient stack, with a triangle isomorphism compatible with that 2-arrow. -/
theorem existsCoequalizerLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (X : StackOver.Groupoids.{u + 1, u, uX, vX} (Scheme.fppfTopology.over S))
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hβ : IsCoequalizerCocycle G f β) :
    ∃ hom : CartesianBasedFunctor (fppfQuotientStack G).p X.p,
      ∃ triangle : (fppfAtlas G).comp hom ≅ f,
        IsCoequalizerCompat G f β hom triangle :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
