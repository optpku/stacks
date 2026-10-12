/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.FiniteGeneration
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.66.9

@stack 058A

The reusable owner separates the textbook exact-association predicate, the
radical-based associated-prime predicate, and their Noetherian set forms.
-/

/- Lemma 10.66.9: a finitely generated ideal is associated exactly when it
is weakly associated. -/
@[stacks 058A "(1) textbook exact-association form"]
#check @Ideal.IsAssociatedToModule.iff_isWeaklyAssociatedToModule_of_fg

@[stacks 058A "(1) radical-based associated-prime form"]
#check @IsAssociatedPrime.iff_isWeaklyAssociatedToModule_of_fg

@[stacks 058A "(2) Noetherian associated-prime equality"]
#check @associatedPrimes.eq_weaklyAssociatedPrimes_of_isNoetherianRing

@[stacks 058A "(2) Noetherian exact associated-prime equality"]
#check @associatedPrimesOfModule.eq_weaklyAssociatedPrimes_of_isNoetherianRing
