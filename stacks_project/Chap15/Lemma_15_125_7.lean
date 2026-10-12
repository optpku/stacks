/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Localization.Bezout
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.125.7

@stack 0AST

The generic localization theorem and its prime-local valuation-ring view are
owned by the Bézout-localization leaf.  This chapter entry contains no local
instance reconstruction.
-/

/- Lemma 15.125.7 (1): localizations of Bézout rings remain Bézout. -/
@[stacks 0AST "Lemma 15.125.7 (1), Bézout localization"]
#check @IsBezout.localization

/- Lemma 15.125.7 (2): prime localizations of Bézout domains are valuation rings. -/
@[stacks 0AST "Lemma 15.125.7 (2), prime localization valuation ring"]
#check @IsBezout.localizationAtPrime_valuationRing

/- Lemma 15.125.7 (3): local Bézout domains are exactly valuation rings. -/
@[stacks 0AST "Lemma 15.125.7 (3), local Bézout characterization"]
#check @ValuationRing.iff_local_bezout_domain
