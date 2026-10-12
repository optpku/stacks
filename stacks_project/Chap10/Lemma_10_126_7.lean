/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.AtPrime.Equiv
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.126.7

@stack 00QS
-/

/- Lemma 10.126.7: an `R`-algebra equivalence between the localizations of two finitely
presented `R`-algebras at prime ideals extends, after shrinking away from those primes, to an
`R`-algebra equivalence between principal-open localizations. -/
@[stacks 00QS "spreading prime-local algebra equivalences"]
#check @Algebra.FinitePresentation.AtPrime.exists_awayAlgEquiv
