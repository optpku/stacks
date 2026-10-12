/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Local.AtPrime
public import ReasLib.RingTheory.Unramified.Basic

/-!
# Formal Unramifiedness at Prime Localizations

This leaf records pairwise local-global criteria for formal unramifiedness and
assembles the equivalent formulations into a localization TFAE.
-/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Pointwise unramifiedness at `q` is equivalent to formal unramifiedness of
the canonical ring homomorphism between the corresponding prime
localizations. -/
theorem isUnramifiedAt_iff_localRingHomAt_formallyUnramified
    (q : PrimeSpectrum S) :
    IsUnramifiedAt R q.asIdeal ↔
      ((algebraMap R S).localRingHomAt q).FormallyUnramified := sorry

/-- Formal unramifiedness is equivalent to formal unramifiedness of every
canonical map between corresponding prime localizations. -/
theorem formallyUnramified_iff_forall_localRingHomAt :
    FormallyUnramified R S ↔
      ∀ q : PrimeSpectrum S,
        ((algebraMap R S).localRingHomAt q).FormallyUnramified := sorry

/-- Formal unramifiedness is equivalent to pointwise unramifiedness over every
target prime and to formal unramifiedness of every induced map between prime
localizations. -/
@[stacks 04E8 "formal unramifiedness at prime localizations"]
theorem formallyUnramified_localization_tfae :
    List.TFAE
      ([
        FormallyUnramified R S,
        ∀ q : PrimeSpectrum S, IsUnramifiedAt R q.asIdeal,
        ∀ q : PrimeSpectrum S,
          ((algebraMap R S).localRingHomAt q).FormallyUnramified
      ] : List Prop) := sorry

end Algebra

namespace Algebra.UnramifiedAt

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- For a finite-type algebra over a Noetherian ring, unramifiedness at a prime
lying over a chosen base prime is equivalent to formal unramifiedness and
essential finite type of the canonical homomorphism between local rings. -/
theorem iff_localRingHom_of_liesOver [IsNoetherianRing A] [Algebra.FiniteType A B]
    (p : Ideal A) [p.IsPrime] (q : PrimeSpectrum B) [q.asIdeal.LiesOver p] :
    Algebra.UnramifiedAt A B q ↔
      (Localization.localRingHom p q.asIdeal (algebraMap A B)
          (q.asIdeal.over_def p)).FormallyUnramified ∧
        (Localization.localRingHom p q.asIdeal (algebraMap A B)
          (q.asIdeal.over_def p)).EssFiniteType := sorry

end Algebra.UnramifiedAt
