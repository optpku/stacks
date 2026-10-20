module

public import Mathlib.RingTheory.LocalProperties.Basic
public import ReasLib.RingTheory.Regular.RingMap

/-!
# Locality of regular ring homomorphisms

This file records that regularity is a local property of commutative ring homomorphisms.
-/

@[expose] public section

namespace RingHom.Regular

/-- Regularity is a local property of commutative ring homomorphisms. -/
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.Regular := sorry

end RingHom.Regular
