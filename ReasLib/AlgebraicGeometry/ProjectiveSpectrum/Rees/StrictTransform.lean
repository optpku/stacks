module

public import ReasLib.RingTheory.ReesAlgebra.Grading.Decomposition
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Topological strict transforms in the projective spectrum of a Rees algebra

Contraction of homogeneous primes gives a map to the prime spectrum of the base
ring. The strict transform of a subset is the closure of its preimage away from
the center.
-/

@[expose] public section

noncomputable section

universe u

namespace ReesAlgebra

variable {A : Type u} [CommRing A]

/-- Contraction along the base algebra map sends a relevant homogeneous prime
of the Rees algebra to a prime of the base ring. -/
def toSpec (I : Ideal A) :
    ProjectiveSpectrum (Grading.grade I) → PrimeSpectrum A :=
  fun x ↦ PrimeSpectrum.comap (algebraMap A (reesAlgebra I))
    ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

/-- The ideal underlying the contraction map is the contraction of the
homogeneous prime along the base algebra map. -/
theorem toSpec_asIdeal (I : Ideal A) (x : ProjectiveSpectrum (Grading.grade I)) :
    (toSpec I x).asIdeal =
      Ideal.comap (algebraMap A (reesAlgebra I)) x.asHomogeneousIdeal.toIdeal := rfl

/-- Contraction from the projective spectrum of a Rees algebra to the prime
spectrum of its base ring is continuous. -/
theorem toSpec_continuous (I : Ideal A) : Continuous (toSpec I) := sorry

/-- The complement of the vanishing locus of the center in the prime spectrum. -/
def openAway (I : Ideal A) : Set (PrimeSpectrum A) :=
  (PrimeSpectrum.zeroLocus (I : Set A))ᶜ

/-- The complement of the center is the complement of its vanishing locus. -/
theorem openAway_def (I : Ideal A) :
    openAway I = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ := rfl

/-- The topological strict transform is the closure of the preimage of a subset
restricted to the complement of the center. -/
def strictTransform (I : Ideal A) (Z : Set (PrimeSpectrum A)) :
    Set (ProjectiveSpectrum (Grading.grade I)) :=
  closure (toSpec I ⁻¹' (Z ∩ openAway I))

/-- The strict transform is computed by taking the closure of the preimage away
from the center. -/
theorem strictTransform_def (I : Ideal A) (Z : Set (PrimeSpectrum A)) :
    strictTransform I Z = closure (toSpec I ⁻¹' (Z ∩ openAway I)) := rfl

/-- The topological strict transform is closed in the projective spectrum of
the Rees algebra. -/
theorem isClosed_strictTransform (I : Ideal A) (Z : Set (PrimeSpectrum A)) :
    IsClosed (strictTransform I Z) := isClosed_closure

end ReesAlgebra
