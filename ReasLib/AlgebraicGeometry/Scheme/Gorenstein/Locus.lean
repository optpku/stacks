module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The Gorenstein locus of a scheme is the set of points whose local rings are Gorenstein. -/
def gorensteinLocus (X : Scheme.{u}) : Set X :=
  {x | IsGorensteinLocalRing (X.presheaf.stalk x)}

/-- Membership in the Gorenstein locus means that the corresponding local ring is Gorenstein. -/
theorem mem_gorensteinLocus (X : Scheme.{u}) (x : X) :
    x ∈ X.gorensteinLocus ↔ IsGorensteinLocalRing (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
