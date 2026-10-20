module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Etale.Complement

/-!
# Étale morphisms over the complement of a closed set
-/

@[expose] public section

universe u

open Algebra AlgebraicGeometry

namespace Algebra

/-- For a finite type algebra over a Noetherian ring, étaleness over the
complement of `V(I)` is equivalent to étaleness of the restricted spectrum map. -/
theorem isEtaleOverComplement_iff_morphismRestrict {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [FiniteType A B] :
    IsEtaleOverComplement I B ↔
      AlgebraicGeometry.Etale
        (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
          ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
            (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩) :=
  sorry

end Algebra
