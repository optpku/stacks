module

public import ReasLib.RingTheory.Henselian.StrictHenselian.AbsolutelyIntegrallyClosed
import StacksCheckRecall

/-!
# Lemma 15.14.7

The strict-Henselian localization theorem is owned by ReasLib; this chapter file is its
source-facing recall.

@stack 0DCS
-/

@[expose] public section

-- The reusable local-ring instance underlying Lemma 15.14.7.
#check @IsAbsolutelyIntegrallyClosed.strictHenselianLocalRing

-- Lemma 15.14.7: localizations at prime ideals are strictly henselian.
@[stacks 0DCS "strict henselianity after localization at a prime"]
#check @IsAbsolutelyIntegrallyClosed.localizationAtPrime_strictHenselian
