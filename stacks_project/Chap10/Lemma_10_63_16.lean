module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization
import StacksCheckRecall

/-!
# Lemma 10.63.16
@stack 05BZ
-/

@[expose] public section

/- Lemma 10.63.16 (Stacks 05BZ): associated primes of a localized module contract to the
associated primes of the original module that survive localization; over a Noetherian ring this
description is an equality. -/

universe u v

section


variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

@[stacks 05BZ "(1)"] #check
  (associatedPrimesOfModule_localizedModule_eq_image_comap (M := M) S :
    Ideal.comap (algebraMap R (Localization S)) ''
        associatedPrimesOfModule (Localization S) (LocalizedModule S M) =
      associatedPrimesOfModule R (LocalizedModule S M))

@[stacks 05BZ "(2)"] #check
  (associatedPrimesOfModule.Localization.inter_disjoint_subset (M := M) S :
    associatedPrimesOfModule R M ∩
        { p : Ideal R | Disjoint (S : Set R) (p : Set R) } ⊆
      associatedPrimesOfModule R (LocalizedModule S M))

section

variable [IsNoetherianRing R]

@[stacks 05BZ "(3)"] #check
  (associatedPrimesOfModule.Localization.inter_disjoint_eq (M := M) S :
    associatedPrimesOfModule R M ∩
        { p : Ideal R | Disjoint (S : Set R) (p : Set R) } =
      associatedPrimesOfModule R (LocalizedModule S M))

end

#check @associatedPrimesOfModule.Localization.inter_range_subset
#check @associatedPrimesOfModule.Localization.inter_range_eq
#check @associatedPrimesOfModule.Localization.mem_localizedModule_iff
#check @associatedPrimes.Localization.inter_disjoint_eq

end
