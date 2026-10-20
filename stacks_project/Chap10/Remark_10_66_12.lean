module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Restriction
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.66.12

@stack 05C7

The three inclusions and the Noetherian equalities are recalled separately.
Together the latter identify all four adjacent sets in the source chain.
-/

/- Remark 10.66.12: the image of the associated primes over S is contained
in the associated primes after restricting scalars. -/
@[stacks 05C7 "associated-prime restriction inclusion"]
#check @associatedPrimesOfModule.Restriction.image_comap_subset

/- Remark 10.66.12: associated primes are weakly associated. -/
@[stacks 05C7 "associated primes are weakly associated"]
#check @associatedPrimesOfModule.subset_weaklyAssociatedPrimes

/- Remark 10.66.12: weakly associated primes after restriction lie in the
contraction image from S. -/
@[stacks 05C7 "weak restriction inclusion"]
#check @weaklyAssociatedPrimes.Restriction.subset_comap_image

/- The source-facing bundled chain, with the four atomic inclusions above. -/
@[stacks 05C7 "source restriction chain"]
#check @associatedPrimesOfModule.Restriction.weaklyAssociatedPrimes_chain

/- If S is Noetherian, the first adjacent inclusion is an equality. -/
@[stacks 05C7 "Noetherian exact restriction equality"]
#check @associatedPrimesOfModule.Restriction.eq_image_comap

/- If S is Noetherian, the middle adjacent inclusion is an equality. -/
@[stacks 05C7 "Noetherian exact/weak equality"]
#check @associatedPrimesOfModule.Restriction.eq_weaklyAssociatedPrimes_of_isNoetherianRing

/- If S is Noetherian, the last adjacent inclusion is an equality. -/
@[stacks 05C7 "Noetherian weak restriction equality"]
#check @weaklyAssociatedPrimes.Restriction.eq_image_comap_of_isNoetherianRing

@[stacks 05C7 "Noetherian source restriction equality chain"]
#check @associatedPrimesOfModule.Restriction.weaklyAssociatedPrimes_eq_chain_of_isNoetherianRing
