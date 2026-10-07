module

public import ReasLib.AlgebraicGeometry.Scheme.K0.CoherentSupport

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.K0'WithSupport

/- Compatibility check for coherent pushforward to supported coherent K₀. -/
#check (AlgebraicGeometry.Scheme.K0'WithSupport.closedPushforward :
  ∀ {X Z : Scheme.{u}} [IsLocallyNoetherian X]
      (i : Z ⟶ X) [IsClosedImmersion i],
    @K0' Z (LocallyOfFiniteType.isLocallyNoetherian i) →+
      K0'WithSupport X (Set.range i.base))

end AlgebraicGeometry.Scheme.K0'WithSupport
