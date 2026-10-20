/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FractionalIdeal.IntegralPart.AssociatedPrime
public import ReasLib.RingTheory.Ideal.AssociatedPrime.PrincipalQuotient
public import ReasLib.RingTheory.Localization.FractionRing.HeightOne
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.157.6

@stack 031T

The source clauses are represented by three reusable layers: principal quotients of `(S₂)`
domains, intersections of height-one localizations in an arbitrary fraction-field model, and
integral parts of principal fractional ideals.  The library statements separate the hypotheses
for absence of embedded primes from those needed for exact height one.
-/

@[stacks 031T "(1), no embedded primes in a principal quotient"]
#check @embeddedAssociatedPrimes.quotient_eq_empty_of_isPrincipal

@[stacks 031T "(1), height of associated primes in a principal quotient"]
#check @associatedPrimes.Quotient.height_eq_one_of_isPrincipal

@[stacks 031T "(2), intersection of height-one localizations"]
#check @PrimeSpectrum.HeightOne.iInf_localization_eq_bot

@[stacks 031T "(3), contraction model for a principal fractional ideal"]
#check @FractionalIdeal.integralPart_spanSingleton

@[stacks 031T "(3), no embedded primes for the contracted fractional ideal"]
#check @FractionalIdeal.IntegralPart.Quotient.spanSingleton_noEmbedded

@[stacks 031T "(3), height for the contracted fractional ideal"]
#check @FractionalIdeal.IntegralPart.Quotient.spanSingleton_associatedPrime_height
