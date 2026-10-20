module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.FiniteTypeInverseSystem

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.FiniteTypeInverseSystem :
  (A : Type u) → [CommRing A] → [TopologicalSpace A] →
    Type (u + 1))
