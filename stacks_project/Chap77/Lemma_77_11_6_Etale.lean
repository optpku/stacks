module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_29_2
public import stacks_project.Chap67.Lemma_67_15_2
public import stacks_project.Chap67.Lemma_67_23_2
public import stacks_project.Chap67.Lemma_67_39_9
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap77.«77_11_4_1_Functor»

/-!
# Étale pullback of flat-in-dimensions functors on algebraic spaces

This module compares the flat-in-dimensions subfunctors of a module and its
pullback along an étale morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsSubfunctor

/-- The relative assassin of `ℱ` in `|X|` over `Y`: points arising from a weakly
associated point of `ℱ` on an étale scheme chart of a field fibre of `f`. -/
def relativeAssassin {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ℱ : X.Modules) : Set (Points X) :=
  {x | ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p))
      (U : smallEtaleSite (fieldFiber f p)) (u : U.left.left),
    Points.mk p = Points.map f x ∧
      Points.map (fiberι f p) t = x ∧
      Points.map U.hom (ofOver.pointsEquiv U.left u) = t ∧
      u ∈ ((Modules.restrictToScheme U).obj
        ((Modules.pullback (fiberι f p)).obj ℱ)).weakAss}

/-- Membership in the flattening-side relative assassin is the étale-chart fibre
condition. -/
theorem mem_relativeAssassin_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (ℱ : X.Modules) (x : Points X) :
    x ∈ relativeAssassin f ℱ ↔
      ∃ (p : FieldValuedPoint Y) (t : Points (fieldFiber f p))
          (U : smallEtaleSite (fieldFiber f p)) (u : U.left.left),
        Points.mk p = Points.map f x ∧
          Points.map (fiberι f p) t = x ∧
          Points.map U.hom (ofOver.pointsEquiv U.left u) = t ∧
          u ∈ ((Modules.restrictToScheme U).obj
            ((Modules.pullback (fiberι f p)).obj ℱ)).weakAss := sorry

/-- Pulling a finite-type quasicoherent module back along an étale morphism enlarges its
flat-in-dimensions subfunctor. -/
theorem le_of_etale {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (n : ℕ) (h : X' ⟶ X) [Etale h] :
    flatInDimensionsSubfunctor f ℱ n ≤
      flatInDimensionsSubfunctor (h ≫ f) ((Modules.pullback h).obj ℱ) n := sorry

/-- If the image of an étale morphism contains the relative assassin of a finite-type
quasicoherent module, pulling back along that morphism preserves its flat-in-dimensions
subfunctor. -/
theorem eq_of_relativeAssassin_subset_range {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (n : ℕ) (h : X' ⟶ X) [Etale h]
    (h_ass : relativeAssassin f ℱ ⊆ Set.range (Points.map h)) :
    flatInDimensionsSubfunctor f ℱ n =
      flatInDimensionsSubfunctor (h ≫ f) ((Modules.pullback h).obj ℱ) n := sorry

end AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsSubfunctor
