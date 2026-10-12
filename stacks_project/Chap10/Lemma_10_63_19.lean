/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.ProductInjective
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.63.19

@stack 0311

The source map is assembled directly from `associatedPrimes` and the canonical
localized-module maps. Its injectivity is owned by the shared associated-prime
leaf and recalled here.
-/

/- Lemma 10.63.19: if `R` is Noetherian, then the canonical map from `M` to the product of its
localizations at the associated primes of `M` is injective. -/
@[stacks 0311]
#check @associatedPrimes.localizationProduct_injective

@[stacks 0311 "associated-prime index"]
#check @associatedPrimes

@[stacks 0311 "canonical localization map"]
#check @LocalizedModule.mkLinearMap
