/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

@[stacks 00IH "(1) values of an ideal"]
#check @ValuationRing.mem_idealOrderIso

@[stacks 00IH "(1) ideal of an order ideal"]
#check @ValuationRing.mem_idealOrderIso_symm

@[stacks 00IH "(1) zero ideal"]
#check @ValuationRing.idealOrderIso_bot

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
