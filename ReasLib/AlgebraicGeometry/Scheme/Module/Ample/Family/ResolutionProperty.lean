module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.CoveringIdeals

/-!
# Resolution property from ample families

An ample family of invertible modules on a scheme yields the resolution property.
-/

@[expose] public section

open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

/-- An ample family of invertible modules on a scheme implies the resolution property. -/
theorem hasResolutionProperty_of_ampleFamily {X : Scheme.{u}} {ι : Type v}
    (L : ι → X.Modules) (hL : Modules.AmpleFamily L) : HasResolutionProperty X := sorry

end AlgebraicGeometry.Scheme
