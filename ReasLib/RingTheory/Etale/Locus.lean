module

public import Mathlib.RingTheory.Smooth.Fiber
public import ReasLib.RingTheory.Etale.LocalRing
public import ReasLib.RingTheory.Unramified.Locus

@[expose] public section

universe u v

namespace Algebra.IsEtaleAt

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Étaleness at a prime is equivalent to flatness and unramifiedness at that prime
for a finitely presented algebra. -/
theorem iff_flatAt_and_isUnramifiedAt [Algebra.FinitePresentation A B]
    (q : PrimeSpectrum B) :
    Algebra.IsEtaleAt A q.asIdeal ↔
      (algebraMap A B).FlatAt q ∧ Algebra.IsUnramifiedAt A q.asIdeal := sorry

/-- For a finite-type algebra over a Noetherian ring, étaleness at a prime lying
over a chosen base prime is equivalent to essential étaleness of the canonical
homomorphism between the corresponding local rings. -/
theorem iff_localRingHom_of_liesOver [IsNoetherianRing A] [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsEtaleAt A q ↔
      (Localization.localRingHom p q (algebraMap A B) (q.over_def p)).EssEtale := sorry

end Algebra.IsEtaleAt

end
