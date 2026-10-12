/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

universe u v

namespace ProjectiveSpectrum

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The underlying prime spectrum point associated to a point of the projective spectrum. -/
def toPrimeSpectrum (x : ProjectiveSpectrum 𝒜) : PrimeSpectrum A :=
  { asIdeal := x.asHomogeneousIdeal.toIdeal
    isPrime := x.isPrime }

/-- The projective distinguished open is the preimage of the corresponding ordinary distinguished open. -/
theorem basicOpen_eq_preimage (f : A) :
    (ProjectiveSpectrum.basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜)) =
      toPrimeSpectrum 𝒜 ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := sorry

/-- The projective zero locus is the preimage of the corresponding ordinary zero locus. -/
theorem zeroLocus_eq_preimage (s : Set A) :
    ProjectiveSpectrum.zeroLocus 𝒜 s =
      toPrimeSpectrum 𝒜 ⁻¹' PrimeSpectrum.zeroLocus s := sorry

end ProjectiveSpectrum
