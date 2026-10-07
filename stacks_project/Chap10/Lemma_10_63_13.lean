module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Restriction
import StacksCheckRecall

/-!
# Lemma 10.63.13

@stack 05DZ
-/

@[expose] public section

/- Lemma 10.63.13 (Stacks 05DZ): restriction of scalars along a Noetherian
scalar ring identifies associated primes with the contractions of associated
primes over that scalar ring. -/

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [IsNoetherianRing S]

@[stacks 05DZ] #check
  (associatedPrimesOfModule.Restriction.eq_image_comap (R := R) (M := M) :
    Ideal.comap (algebraMap R S) '' associatedPrimesOfModule S M =
      associatedPrimesOfModule R M)

@[stacks 05DZ "associated-prime set companion"]
#check
  (associatedPrimes.Restriction.eq_image_comap (R := R) (M := M) :
    Ideal.comap (algebraMap R S) '' associatedPrimes S M = associatedPrimes R M)

end
