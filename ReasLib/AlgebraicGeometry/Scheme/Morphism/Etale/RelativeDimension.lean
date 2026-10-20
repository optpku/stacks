module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- A morphism of schemes is étale exactly when it is smooth of relative dimension zero. -/
theorem etale_iff_smoothOfRelativeDimension_zero {X S : Scheme.{u}} (f : X ⟶ S) :
    Etale f ↔ SmoothOfRelativeDimension 0 f := sorry

end Scheme.Hom

end AlgebraicGeometry
