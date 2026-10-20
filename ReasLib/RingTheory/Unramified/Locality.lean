module

public import ReasLib.RingTheory.Unramified.Basic

/-!
# Locality of unramified ring homomorphisms

This file records that unramifiedness and G-unramifiedness are local properties
of commutative ring homomorphisms.
-/

@[expose] public section

namespace RingHom.Unramified

/-- Unramifiedness is a local property of commutative ring homomorphisms. -/
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.Unramified := sorry

end RingHom.Unramified

namespace RingHom.GUnramified

/-- G-unramifiedness is a local property of commutative ring homomorphisms. -/
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.GUnramified := sorry

end RingHom.GUnramified
