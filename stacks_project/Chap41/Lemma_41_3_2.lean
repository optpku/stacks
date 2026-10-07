module

public import ReasLib.RingTheory.Unramified.Locus
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 41.3.2: for a finite-type algebra over a Noetherian ring, unramifiedness at a
prime `q` lying over `p` is equivalent to formal unramifiedness and essential finite type of
the canonical local homomorphism `Aₚ → B_q`. -/
@[stacks 039G] #check
  (Algebra.UnramifiedAt.iff_localRingHom_of_liesOver :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [Algebra.FiniteType A B]
      (p : Ideal A) [p.IsPrime] (q : PrimeSpectrum B) [q.asIdeal.LiesOver p],
      Algebra.UnramifiedAt A B q ↔
        (Localization.localRingHom p q.asIdeal (algebraMap A B)
            (q.asIdeal.over_def p)).FormallyUnramified ∧
          (Localization.localRingHom p q.asIdeal (algebraMap A B)
            (q.asIdeal.over_def p)).EssFiniteType)
