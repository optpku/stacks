module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open CategoryTheory AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Smooth morphisms of schemes are universally locally acyclic. -/
instance UniversallyLocallyAcyclic.of_smooth {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] : UniversallyLocallyAcyclic f :=
  sorry

end AlgebraicGeometry.Scheme
