module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.LocalGeneration

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
    (h_ass : Set.Subset (Modules.RelativeWeakAss.existsField f ℱ)
      (Set.range (Points.map h))) :
    flatInDimensionsSubfunctor f ℱ n =
      flatInDimensionsSubfunctor (h ≫ f) ((Modules.pullback h).obj ℱ) n := sorry

end AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsSubfunctor
