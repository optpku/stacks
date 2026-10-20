module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Connected

/-!
# Proper geometrically normal schemes over a field

This file relates global sections, connectedness, irreducibility, and integrality for proper
geometrically normal schemes over a field.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

namespace geometricallyNormal

variable {k : Type u} [Field k]

/-- For a proper geometrically normal scheme over a field, the canonical map from the field to
global sections is bijective exactly when the scheme is geometrically connected. -/
theorem globalSectionsMap_bijective_iff_geometricallyConnected
    (X : SchemeOverField k) [IsProper X.hom] (hX : geometricallyNormal X) :
    Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ↔
      GeometricallyConnected X.hom := sorry

/-- A proper geometrically normal scheme over a field is geometrically connected exactly when
it is geometrically irreducible. -/
theorem geometricallyConnected_iff_geometricallyIrreducible
    (X : SchemeOverField k) [IsProper X.hom] (hX : geometricallyNormal X) :
    GeometricallyConnected X.hom ↔ GeometricallyIrreducible X.hom := sorry

/-- A proper geometrically normal scheme over a field is geometrically irreducible exactly when
it is geometrically integral. -/
theorem geometricallyIrreducible_iff_geometricallyIntegral
    (X : SchemeOverField k) [IsProper X.hom] (hX : geometricallyNormal X) :
    GeometricallyIrreducible X.hom ↔ GeometricallyIntegral X.hom := sorry

/-- For a proper geometrically normal scheme over a field, bijectivity of the canonical map to
global sections, geometric connectedness, geometric irreducibility, and geometric integrality
are equivalent. -/
theorem proper_globalSections_tfae
    (X : SchemeOverField k) [IsProper X.hom] (hX : geometricallyNormal X) :
    List.TFAE
      [ Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)
      , GeometricallyConnected X.hom
      , GeometricallyIrreducible X.hom
      , GeometricallyIntegral X.hom
      ] := sorry

end geometricallyNormal

end AlgebraicGeometry.SchemeOverField
