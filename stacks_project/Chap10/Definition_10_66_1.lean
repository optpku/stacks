module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.66.1

@stack 0547

Weak association is neutral commutative-algebra infrastructure owned by
`ReasLib.RingTheory.Ideal.AssociatedPrime.Weak`.
-/

/- Definition 10.66.1 (Stacks 0547): `Ideal.IsWeaklyAssociatedToModule R M 𝔭`
means that `𝔭` is minimal over the annihilator of an element of `M`. -/
@[stacks 0547]
#check @Ideal.IsWeaklyAssociatedToModule

/- The canonical set owner and its elementary structural API. -/
@[stacks 0547 "weakly associated prime set"]
#check @weaklyAssociatedPrimes
@[stacks 0547 "weakly associated prime membership"]
#check @mem_weaklyAssociatedPrimes_iff
@[stacks 0547 "invariance under linear equivalence"]
#check @LinearEquiv.weaklyAssociatedPrimes_eq
@[stacks 0547 "subsingleton module"]
#check @weaklyAssociatedPrimes.eq_empty_of_subsingleton
@[stacks 0547 "nontrivial module"]
#check @weaklyAssociatedPrimes.nonempty
