/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.Extension.Etale
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.124.5 (0ASJ)

The localized valuation-ring extension and its weak unramifiedness are owned by the ReasLib
etale-branch API.

@stack 0ASJ
-/

/- Lemma 15.124.5 (1): the localized etale branch is an extension of valuation rings. -/
@[stacks 0ASJ "Lemma 15.124.5 (1): etale branch extension of valuation rings"]
#check @Algebra.Etale.localizationAtPrime_isExtensionOfValuationRings

/- Lemma 15.124.5 (2): the localized extension is weakly unramified. -/
@[stacks 0ASJ "Lemma 15.124.5 (2): etale branch is weakly unramified"]
#check @Algebra.Etale.localizationAtPrime_weaklyUnramified

#check @Algebra.Etale.localizationAtPrime_isDomain
#check @Algebra.Etale.localizationAtPrime_valuationRing

end
