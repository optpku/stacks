module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsBlowup

/-- The blowup of the spectrum of a two-dimensional regular local ring at its maximal ideal is
irreducible. -/
theorem irreducibleSpace_of_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    IrreducibleSpace X := sorry

/-- The blowup of the spectrum of a two-dimensional regular local ring at its maximal ideal is a
regular scheme. -/
theorem regular_of_maximalIdeal (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    Scheme.Regular X := sorry

end AlgebraicGeometry.IsBlowup
