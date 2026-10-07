module

public import Mathlib.RingTheory.Etale.StandardEtale
public import ReasLib.RingTheory.Polynomial.Splitting
import StacksCheckRecall

/-!
# Finite faithfully flat étale neighborhoods

@stack 00UF

The standard-étale presentation, polynomial root lifting, and residue-field calculations in the
source proof are implementation details.  The stable chapter surface is the finite,
finitely-presented, faithfully-flat extension together with its prime-local factorization data.
-/

@[expose] public section

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsStandardEtale R S]

/-- Lemma 10.144.5 (00UF): a standard étale `R`-algebra admits a finite, finitely presented,
faithfully flat extension whose localizations factor the given algebra at every pair of primes over
the same prime of `R`. -/
@[stacks 00UF]
theorem exists_finitePresentation_flat_surjective_extension_lifting_primes :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) (q' : p.asIdeal.primesOver S'),
          ∃ (g' : S') (_ : g' ∉ q'.1) (φ : S →ₐ[R] Localization.Away g'),
            Ideal.comap φ.toRingHom (Ideal.map (algebraMap S' (Localization.Away g')) q'.1) =
              q.1 := sorry

end

end Algebra

@[stacks 00UF "source bridge"]
#check @Algebra.exists_finitePresentation_flat_surjective_extension_lifting_primes
@[stacks 00UF "splitting extension support"]
#check @Polynomial.Monic.exists_syntomic_faithfullyFlat_splits_map
#print axioms Algebra.exists_finitePresentation_flat_surjective_extension_lifting_primes
