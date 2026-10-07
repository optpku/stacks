module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CoordinateCenter
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalTwist

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Blowup.CoordinateCenter

/-- The exceptional-twist comparison for a coordinate-center blowup is an isomorphism in the
derived category for every locally free module and every `i : Fin n`. -/
@[instance]
theorem exceptionalTwistComparison_isIso
    (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (𝓔 : (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))).Modules)
    [𝓔.IsLocallyFree] (i : Fin n) :
    IsIso (π.exceptionalTwistComparison 𝓔 i) := sorry

end AlgebraicGeometry.Blowup.CoordinateCenter
