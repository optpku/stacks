module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalProjectiveBundle
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.TwistingSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- For the blowup of the spectrum of a two-dimensional regular local ring at its maximal ideal,
the relative differential sheaf is isomorphic to the pushforward of the relative differential sheaf
of the exceptional divisor over the closed center. -/
theorem relativeDifferentials_isIsomorphic_pushforward_exceptional
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (h_dim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsBlowup f (Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A))] :
    let I := Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal A)
    let E := exceptionalIdeal (IsLocalRing.maximalIdeal A) f
    IsIsomorphic Ω[f.toShHom]
      ((Scheme.Modules.pushforward E.subschemeι).obj Ω[(exceptionalProjection I f).toShHom]) := sorry

end AlgebraicGeometry.IsBlowup
