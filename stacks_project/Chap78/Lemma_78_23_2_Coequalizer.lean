module

public import stacks_project.Chap78.Lemma_78_20_2_Atlas
public import stacks_project.Chap78.Lemma_78_20_3_Comparison
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver

/-!
# Weak 2-coequalizer property of a quotient stack

This module records the cocycle identity on a general 2-arrow `β : f ∘ s ⟶ f ∘ t` and the
factorization of such data through the quotient stack `[U/R]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Left whiskering of a 2-arrow `β : f ∘ s ⟶ f ∘ t` by the cartesian 1-morphism associated
to `φ : Y ⟶ G.R.left`. -/
def compWhisker {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {Y : AlgebraicSpace S} (φ : Y ⟶ G.R.left)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    {f : CartesianBasedFunctor (stackInSets G.U.left).p X.p}
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f) :
    (stackInSets.map φ).comp ((stackInSets.map G.s.left).comp f) ⟶
      (stackInSets.map φ).comp ((stackInSets.map G.t.left).comp f) :=
  (CartesianBasedFunctor.precomp X.p (stackInSets.map φ)).map β

/-- `compWhisker G φ β` is precomposition of `β` along `stackInSets.map φ`. -/
theorem compWhisker_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Y : AlgebraicSpace S} (φ : Y ⟶ G.R.left)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    {f : CartesianBasedFunctor (stackInSets G.U.left).p X.p}
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f) :
    compWhisker G φ β =
      (CartesianBasedFunctor.precomp X.p (stackInSets.map φ)).map β :=
  sorry

/-- The composites `f ∘ s ∘ pr₁` and `f ∘ s ∘ c` agree as cartesian 1-morphisms, where `pr₁`
is `(pullback.snd G.s G.t).left` and `c` is `G.c.left`. -/
theorem compWhisker_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p) :
    (stackInSets.map (pullback.snd G.s G.t).left).comp
        ((stackInSets.map G.s.left).comp f) =
      (stackInSets.map G.c.left).comp ((stackInSets.map G.s.left).comp f) :=
  sorry

/-- The composites `f ∘ t ∘ pr₁` and `f ∘ s ∘ pr₀` agree as cartesian 1-morphisms, where
`pr₀` is `(pullback.fst G.s G.t).left` and `pr₁` is `(pullback.snd G.s G.t).left`. -/
theorem compWhisker_middle {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
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
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p) :
    (stackInSets.map (pullback.fst G.s G.t).left).comp
        ((stackInSets.map G.t.left).comp f) =
      (stackInSets.map G.c.left).comp ((stackInSets.map G.t.left).comp f) :=
  sorry

/-- The source cocycle identity `β ★ id_c = (β ★ id_pr₀) ∘ (β ★ id_pr₁)` on a 2-arrow
`β : f ∘ s ⟶ f ∘ t`, written in diagrammatic order with `pr₁` first. -/
def IsCoequalizerCocycle {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f) : Prop :=
  eqToHom (compWhisker_source G f).symm ≫
      compWhisker G (pullback.snd G.s G.t).left β ≫
      eqToHom (compWhisker_middle G f) ≫
      compWhisker G (pullback.fst G.s G.t).left β ≫
      eqToHom (compWhisker_target G f) =
    compWhisker G G.c.left β

/-- Unfolding of `IsCoequalizerCocycle` as the whisker identity on `β`. -/
theorem IsCoequalizerCocycle.eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hβ : IsCoequalizerCocycle G f β) :
    eqToHom (compWhisker_source G f).symm ≫
        compWhisker G (pullback.snd G.s G.t).left β ≫
        eqToHom (compWhisker_middle G f) ≫
        compWhisker G (pullback.fst G.s G.t).left β ≫
        eqToHom (compWhisker_target G f) =
      compWhisker G G.c.left β :=
  sorry

/-- `IsCoequalizerCocycle` is equivalent to the whisker identity on `β`. -/
theorem IsCoequalizerCocycle.iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f) :
    IsCoequalizerCocycle G f β ↔
      eqToHom (compWhisker_source G f).symm ≫
          compWhisker G (pullback.snd G.s G.t).left β ≫
          eqToHom (compWhisker_middle G f) ≫
          compWhisker G (pullback.fst G.s G.t).left β ≫
          eqToHom (compWhisker_target G f) =
        compWhisker G G.c.left β :=
  sorry

/-- Associativity identifying `(π ∘ s) ∘ g` with `s` then `π ∘ g`. -/
theorem atlasSource_comp_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (hom : CartesianBasedFunctor (quotientStack G).p X.p) :
    (atlasSource G).comp hom =
      (stackInSets.map G.s.left).comp ((atlas G).comp hom) :=
  sorry

/-- Associativity identifying `(π ∘ t) ∘ g` with `t` then `π ∘ g`. -/
theorem atlasTarget_comp_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (hom : CartesianBasedFunctor (quotientStack G).p X.p) :
    (atlasTarget G).comp hom =
      (stackInSets.map G.t.left).comp ((atlas G).comp hom) :=
  sorry

/-- Compatibility of `g ★ α` with `β` after transporting along a triangle 2-isomorphism. -/
def IsCoequalizerCompat {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hom : CartesianBasedFunctor (quotientStack G).p X.p)
    (triangle : (atlas G).comp hom ≅ f) : Prop :=
  eqToHom (atlasSource_comp_hom G hom) ≫
      (CartesianBasedFunctor.precomp X.p (stackInSets.map G.s.left)).map triangle.hom ≫
      β =
    (CartesianBasedFunctor.postcomp (stackInSets G.R.left).p hom).map (sourceTarget G) ≫
      eqToHom (atlasTarget_comp_hom G hom) ≫
        (CartesianBasedFunctor.precomp X.p (stackInSets.map G.t.left)).map triangle.hom

/-- Unfolding of `IsCoequalizerCompat` as an equality of 2-arrows. -/
theorem IsCoequalizerCompat.eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    {X : StackOver.Groupoids (Scheme.fppfTopology.over S)}
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hom : CartesianBasedFunctor (quotientStack G).p X.p)
    (triangle : (atlas G).comp hom ≅ f)
    (h : IsCoequalizerCompat G f β hom triangle) :
    eqToHom (atlasSource_comp_hom G hom) ≫
        (CartesianBasedFunctor.precomp X.p (stackInSets.map G.s.left)).map triangle.hom ≫
        β =
      (CartesianBasedFunctor.postcomp (stackInSets G.R.left).p hom).map (sourceTarget G) ≫
        eqToHom (atlasTarget_comp_hom G hom) ≫
          (CartesianBasedFunctor.precomp X.p (stackInSets.map G.t.left)).map triangle.hom :=
  sorry

/-- A factorization of `f` through `[U/R]` together with the triangle 2-isomorphism and
compatibility of `g ★ α` with `β`. -/
structure CoequalizerLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (X : StackOver.Groupoids (Scheme.fppfTopology.over S))
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f) where
  /-- The factorization 1-morphism `[U/R] ⟶ X`. -/
  hom : CartesianBasedFunctor (quotientStack G).p X.p
  /-- The triangle 2-isomorphism identifying `f` with `π` then the lift. -/
  triangle : (atlas G).comp hom ≅ f
  /-- Compatibility of the whiskered atlas cell `sourceTarget G` with `β`. -/
  compat : IsCoequalizerCompat G f β hom triangle

/-- Existence of a 1-morphism `[U/R] ⟶ X` making the atlas triangle 2-commute, given a
cocycle 2-arrow `β : f ∘ s ⟶ f ∘ t`. -/
theorem existsCoequalizerLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (X : StackOver.Groupoids (Scheme.fppfTopology.over S))
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hβ : IsCoequalizerCocycle G f β) :
    Nonempty (CoequalizerLift G X f β) :=
  sorry

/-- A selected factorization of `f` through `[U/R]` associated to a cocycle 2-arrow `β`. -/
noncomputable def coequalizerLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (X : StackOver.Groupoids (Scheme.fppfTopology.over S))
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hβ : IsCoequalizerCocycle G f β) :
    CoequalizerLift G X f β :=
  Classical.choice (existsCoequalizerLift G X f β hβ)

/-- The selected 1-morphism `[U/R] ⟶ X` of `coequalizerLift`. -/
theorem coequalizerLift_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (X : StackOver.Groupoids (Scheme.fppfTopology.over S))
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hβ : IsCoequalizerCocycle G f β) :
    (coequalizerLift G X f β hβ).hom =
      (Classical.choice (existsCoequalizerLift G X f β hβ)).hom :=
  sorry

/-- The selected triangle 2-isomorphism of `coequalizerLift`. -/
theorem coequalizerLift_triangle {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (X : StackOver.Groupoids (Scheme.fppfTopology.over S))
    (f : CartesianBasedFunctor (stackInSets G.U.left).p X.p)
    (β : (stackInSets.map G.s.left).comp f ⟶ (stackInSets.map G.t.left).comp f)
    (hβ : IsCoequalizerCocycle G f β) :
    (coequalizerLift G X f β hβ).triangle =
      (Classical.choice (existsCoequalizerLift G X f β hβ)).triangle :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
