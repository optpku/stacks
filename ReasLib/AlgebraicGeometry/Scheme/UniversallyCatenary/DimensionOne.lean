module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.DimensionOne

/-!
# Universal catenarity of one-dimensional affine schemes

The spectrum of a one-dimensional Noetherian domain is universally catenary.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.UniversallyCatenary

/-- The spectrum of a one-dimensional Noetherian domain is universally catenary. -/
theorem specOfDimOneDomain
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) :
    AlgebraicGeometry.UniversallyCatenary (Spec (CommRingCat.of A)) := sorry

end AlgebraicGeometry.UniversallyCatenary
