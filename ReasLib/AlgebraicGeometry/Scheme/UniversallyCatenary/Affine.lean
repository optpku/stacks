module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Locality

/-!
# Universal catenarity of affine schemes

This module transfers universal catenarity from a ring to its prime spectrum.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The spectrum of a universally catenary ring is universally catenary. -/
instance instUniversallyCatenarySpec {R : Type u} [CommRing R]
    [UniversallyCatenaryRing.{u, u} R] :
    UniversallyCatenary (Spec (CommRingCat.of R)) := sorry

end AlgebraicGeometry
