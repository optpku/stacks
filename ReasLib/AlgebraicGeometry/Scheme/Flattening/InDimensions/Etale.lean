module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

/-!
# Étale pullback of flat-in-dimensions functors

This module compares the flat-in-dimensions subfunctors of a module and its pullback along an
étale morphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Flattening.flatInDimensionsSubfunctor

/-- Pulling a finite-type quasicoherent module back along an étale morphism enlarges its
flat-in-dimensions subfunctor. -/
theorem le_of_etale {X X' S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)
    (h : X' ⟶ X) [Etale h] :
    flatInDimensionsSubfunctor f ℱ n ≤
      flatInDimensionsSubfunctor (h ≫ f) ((Scheme.Modules.pullback h).obj ℱ) n := sorry

/-- If the image of an étale morphism contains the relative assassin of a finite-type
quasicoherent module, pulling back along that morphism preserves its flat-in-dimensions
subfunctor. -/
theorem eq_of_relativeAssassin_subset_range {X X' S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)
    (h : X' ⟶ X) [Etale h]
    (h_ass : Scheme.Modules.relativeAssassin f ℱ ⊆ Set.range h.base) :
    flatInDimensionsSubfunctor f ℱ n =
      flatInDimensionsSubfunctor (h ≫ f) ((Scheme.Modules.pullback h).obj ℱ) n := sorry

end AlgebraicGeometry.Scheme.Flattening.flatInDimensionsSubfunctor
