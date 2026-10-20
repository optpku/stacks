module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Étale morphisms over locally Noetherian schemes

This module records the locally Noetherian property of the source of a bundled étale scheme.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The source of an étale morphism to a locally Noetherian scheme is locally Noetherian. -/
instance instIsLocallyNoetherianLeft {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.Etale) : IsLocallyNoetherian U.left := sorry

end AlgebraicGeometry.Scheme.Etale
