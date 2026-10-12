/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FormalFiber.PRing
import StacksCheckRecall

/-!
# Lemma 15.51.1

@stack 0BIS
-/

@[expose] public section

/- Lemma 15.51.1, tag `0BIS`: a Noetherian ring is a `P`-ring exactly when every formal
fiber attached to an inclusion of primes `q ≤ p` has property `P`. -/
@[stacks 0BIS "prime-pair criterion for P-rings"]
#check @IsPRing.iff_holdsOnPrimePairFibers

/- Formal fibers of the fixed localization `R_p` are indexed by primes `q ≤ p` of `R`. -/
#check @FieldAlgebraProperty.holdsOnFormalFibers_localizationAtPrime_iff

/- Prime localization preserves the stronger `P`-ring condition. -/
#check @IsPRing.localizationAtPrime

/- Conversely, the `P`-ring condition can be assembled from all prime localizations. -/
#check @IsPRing.of_localizationsAtPrime
