module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [CommRing A]

/-- The union of the `J'`-primary components whose vanishing loci agree with that of `J`
after intersection with `PrimeSpectrum.zeroLocus I`. -/
def supportColimit (I J : Ideal A) (M : ModuleCat.{u} A) : Submodule A M :=
  sSup { N | ∃ J' : Ideal A,
    J' ≤ J ∧
      PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
      N = J'.primaryComponent M }

/-- Every primary component with the prescribed vanishing-locus condition is contained in
the corresponding support colimit. -/
theorem primaryComponent_le_supportColimit (I J J' : Ideal A) (M : ModuleCat.{u} A)
    (hJ' : J' ≤ J)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    J'.primaryComponent M ≤ supportColimit I J M := sorry

/-- The primary components defining a support colimit form a nonempty directed family. -/
theorem supportComponents_directed (I J : Ideal A) (M : ModuleCat.{u} A) :
    Set.Nonempty { N : Submodule A M | ∃ J' : Ideal A,
      J' ≤ J ∧
        PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
        N = J'.primaryComponent M } ∧
    DirectedOn (· ≤ ·) { N : Submodule A M | ∃ J' : Ideal A,
      J' ≤ J ∧
        PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
        N = J'.primaryComponent M } := sorry

/-- Membership in a support colimit is membership in one of its defining primary
components. -/
theorem mem_supportColimit (I J : Ideal A) (M : ModuleCat.{u} A) (x : M) :
    x ∈ supportColimit I J M ↔
      ∃ J' : Ideal A, J' ≤ J ∧
        PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
        x ∈ J'.primaryComponent M := sorry

end Ideal
