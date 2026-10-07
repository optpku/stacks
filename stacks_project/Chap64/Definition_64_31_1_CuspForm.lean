module

public import ReasLib.NumberTheory.Automorphic.CuspForm

open AlgebraicGeometry

/- The unramified cusp-form API is owned by `ReasLib.NumberTheory.Automorphic.CuspForm`. -/
#check (AlgebraicGeometry.SchemeOverField.UnramifiedCuspForm :
  ∀ {k : Type*} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    (Λ : Type _) [Ring Λ] [Fintype k] [Invertible (ringChar k : Λ)], Type _)
