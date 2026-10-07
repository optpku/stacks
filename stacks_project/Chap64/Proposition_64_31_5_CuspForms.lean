module

public import ReasLib.NumberTheory.Automorphic.CuspForms

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField

universe u v

/- Fixed-character unramified cusp forms are owned by the invariant cuspidal submodule. -/
#check (AlgebraicGeometry.SchemeOverField.CuspForms :
  ∀ {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    (Λ : Type v) [CommRing Λ] [Invertible (ringChar k : Λ)]
    (character : closedPoints X.left → Λˣ), Type _)
