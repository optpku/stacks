/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.OverField.PresentationAtPrime
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.135.4

@stack 00SC

The five presentation criteria and the terminal cotangent-generator assertion are owned by
`Algebra.PolynomialPresentationAtPrime`.
-/

@[stacks 00SC "five presentation criteria at a prime"]
#check @Algebra.PolynomialPresentationAtPrime.tfae

@[stacks 00SC "cotangent generators form a regular sequence"]
#check @Algebra.PolynomialPresentationAtPrime.cotangentGeneratorsFormRegularSequence

/- Canonical local-presentation data used in the source statement. -/
#check @Algebra.PolynomialPresentationAtPrime.localizedKernelIdeal
#check @Algebra.PolynomialPresentationAtPrime.localQuotientRing
#check @Algebra.PolynomialPresentationAtPrime.localizedConormalModule
