/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Henselization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.124.6

@stack 0ASK

This is the source-facing recall for the henselization tower.  The reusable
domain, valuation-ring, extension, and weakly-unramified owners live in the
valuation Henselization leaf; this chapter file deliberately contains only
the tagged checks and the source-shaped tower check.
-/

/- Lemma 15.124.6 (1): the henselization map is weakly unramified. -/
@[stacks 0ASK "Lemma 15.124.6 (1), henselization weakly unramified"]
#check @ValuationRing.Henselization.weaklyUnramified

/- Lemma 15.124.6 (2): the strict henselization map is weakly unramified. -/
@[stacks 0ASK "Lemma 15.124.6 (2), strict henselization weakly unramified"]
#check @ValuationRing.StrictHenselization.weaklyUnramified

/- Lemma 15.124.6 (3): the two maps in the henselization tower are weakly unramified. -/
@[stacks 0ASK "Lemma 15.124.6 (3), henselization tower"]
#check @ValuationRing.StrictHenselization.tower_weaklyUnramified

/- The structural consequences are named theorems rather than ambiguous target-only instances. -/
#check @ValuationRing.Henselization.domain_of_henselization
#check @ValuationRing.Henselization.valuationRing_of_henselization
#check @ValuationRing.Henselization.extension_instance
#check @ValuationRing.StrictHenselization.domain_of_strictHenselization
#check @ValuationRing.StrictHenselization.valuationRing_of_strictHenselization
#check @ValuationRing.StrictHenselization.extension_instance
