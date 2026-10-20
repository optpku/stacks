module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.RelativeDimension

/-!
# Flat pullback along finite locally free morphisms

This file records the push-pull formula for cycles along finite locally free morphisms of
constant rank.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- For a finite locally free morphism of constant rank `d`, pushing forward a flat pullback
of a cycle is multiplication by `d`. -/
theorem mapHom_flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (d : ℕ) [IsFiniteLocallyFreeOfRank f.left d]
    (k : ℤ) (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k) :
    mapHom f.left (X.hom.relativeDimensionFunction δ)
        (Y.hom.relativeDimensionFunction δ) k
        (reindex (X.hom.relativeDimensionFunction δ) (add_zero k)
          (flatPullback δ X Y f 0 k α)) =
      d • α := sorry

end AlgebraicGeometry.CycleGroup
