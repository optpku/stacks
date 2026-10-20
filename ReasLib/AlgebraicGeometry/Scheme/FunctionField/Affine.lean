module

public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsDomain A]

/-- A domain acts canonically on the function field of its affine spectrum. -/
noncomputable instance algebraFunctionField :
    Algebra A (Spec (CommRingCat.of A)).functionField :=
  instAlgebraCarrierFunctionFieldSpec (CommRingCat.of A)

/-- The function field of the affine spectrum of a domain is its canonical fraction ring. -/
instance isFractionRingFunctionField :
    IsFractionRing A (Spec (CommRingCat.of A)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of A)

end AlgebraicGeometry
