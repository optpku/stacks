module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.FiniteSeparable
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.FiniteSeparable

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GeometricallyConnected

/-- A fibre is geometrically connected exactly when every pointed étale neighbourhood
gives a connected base-changed fibre. -/
@[stacks 03GZ]
theorem iff_connectedSpace_etaleNeighborhood {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    GeometricallyConnected (f.fiberToSpecResidueField s) ↔
      ∀ U : Scheme.EtaleNeighborhood S s,
        ConnectedSpace ((pullback.snd f U.toEtale.hom).fiber U.point) := sorry

end AlgebraicGeometry.GeometricallyConnected
