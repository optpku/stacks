module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Jacobson
public import ReasLib.RingTheory.Jacobson.Localization

/-!
# Jacobson complements of closed subsets in affine schemes

The complement of the zero locus of an ideal contained in the Jacobson radical
of a Noetherian ring is Jacobson, with the punctured spectrum of a local ring
and the complement of the Jacobson radical as canonical specializations.
-/

@[expose] public section

open AlgebraicGeometry PrimeSpectrum
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-- For a Noetherian ring, the complement of the zero locus of an ideal contained in the
Jacobson radical is a Jacobson scheme. -/
theorem jacobsonSpace_spec_compl_zeroLocus_of_le_ringJacobson
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    JacobsonSpace
      (Scheme.Opens.toScheme
        (⟨(PrimeSpectrum.zeroLocus (I : Set R))ᶜ,
          (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (.of R)).Opens)) := sorry

/-- The punctured spectrum of a Noetherian local ring is a Jacobson scheme. -/
theorem jacobsonSpace_puncturedSpectrum_of_isNoetherianRing
    [IsLocalRing R] [IsNoetherianRing R] :
    JacobsonSpace (PuncturedSpectrum.scheme R) := sorry

/-- For a Noetherian ring, the complement of the zero locus of its Jacobson radical is a
Jacobson scheme. -/
theorem jacobsonSpace_spec_compl_zeroLocus_ringJacobson
    [IsNoetherianRing R] :
    JacobsonSpace
      (Scheme.Opens.toScheme
        (⟨(PrimeSpectrum.zeroLocus ((Ring.jacobson R : Ideal R) : Set R))ᶜ,
          (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (.of R)).Opens)) := sorry

end AlgebraicGeometry
