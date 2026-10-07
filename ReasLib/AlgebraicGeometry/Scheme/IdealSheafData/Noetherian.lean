module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Immersion.Noetherian

/-!
# Noetherian closed subschemes

This file supplies the canonical locally Noetherian and Noetherian instances for the closed
subscheme cut out by an ideal sheaf.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The closed subscheme cut out by an ideal sheaf on a locally Noetherian scheme is locally
Noetherian. -/
instance subschemeIsLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : IsLocallyNoetherian I.subscheme :=
  IsLocallyNoetherian.of_isImmersion I.subschemeι

/-- The closed subscheme cut out by an ideal sheaf on a Noetherian scheme is Noetherian. -/
@[stacks 088A "Noetherian closed thickenings"]
instance subschemeIsNoetherian {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : IsNoetherian I.subscheme := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
