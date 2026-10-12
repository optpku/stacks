/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Ideal.ValueGroup
import StacksCheckRecall

@[expose] public section

/-!
@stack 00IH

# Ideals of a valuation ring and ideals of its value group

The order isomorphism is the concrete owner for the source correspondence. Its
prime-ideal compatibility is exposed separately for downstream use.
-/

/- Lemma 10.50.17 (1): ideals of a valuation ring correspond to order ideals in its integral value
cone. -/
@[stacks 00IH "(1) ideal correspondence"]
#check @ValuationRing.idealOrderIso

/- Lemma 10.50.17 (2): the correspondence identifies prime ideals on both sides. -/
@[stacks 00IH "(2) prime ideals"]
#check @ValuationRing.idealOrderIso_isPrime_iff

@[stacks 00IH "integral-cone owner"]
#check @ValuationRing.IntegralCone

@[stacks 00IH "valuation-prime predicate"]
#check @Order.Ideal.IsValuationPrime

#check @ValuationRing.equivInteger
#check @Valuation.leIdeal
#check @RingEquiv.idealComapOrderIso
