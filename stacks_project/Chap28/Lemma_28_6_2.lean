module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R]

/- Lemma 28.6.2: an affine scheme `Spec R` is Jacobson if and only if the ring `R` is Jacobson. -/
@[stacks 01P3] #check
  (PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace (R := R) :
    IsJacobsonRing R ↔ JacobsonSpace (Spec (.of R)))

#check
  ((PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace (R := R)).symm :
    JacobsonSpace (Spec (.of R)) ↔ IsJacobsonRing R)

end AlgebraicGeometry
