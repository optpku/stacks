module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Slicing.Separable
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth.ClosedPoints

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Smooth

/-- A smooth morphism admits a lift over an étale neighbourhood of every point in its
image. -/
theorem exists_etaleNeighborhood_lift
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (s : S) (hs : s ∈ Set.range f) :
    ∃ (U : Scheme.EtaleNeighborhood S s) (g : U.toEtale.left ⟶ X),
      g ≫ f = U.toEtale.hom := sorry

end AlgebraicGeometry.Smooth
