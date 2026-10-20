module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Openness of étale morphisms
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Etale

/-- The underlying map of an étale scheme morphism is an open map. -/
theorem isOpenMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    IsOpenMap f.base := sorry

end AlgebraicGeometry.Etale
