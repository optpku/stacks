module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import ReasLib.RingTheory.Depth
public import Mathlib.RingTheory.Henselian

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (f : maximalIdeal A)

/-- Restriction of finite étale covers along the principal quotient is full
when `A` is a Noetherian local ring of depth at least three and `(A, (f))` is
a henselian pair. -/
instance finiteEtaleBaseChange_full_of_depth
    [HenselianRing A (principalIdeal f)]
    [Fact ((3 : ℕ∞) ≤ moduleDepth A A)] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Full := sorry

/-- Restriction of finite étale covers along the principal quotient is faithful
when `A` is a Noetherian local ring of depth at least three and `(A, (f))` is
a henselian pair. -/
instance finiteEtaleBaseChange_faithful_of_depth
    [HenselianRing A (principalIdeal f)]
    [Fact ((3 : ℕ∞) ≤ moduleDepth A A)] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Faithful := sorry

end AlgebraicGeometry.PuncturedSpectrum
