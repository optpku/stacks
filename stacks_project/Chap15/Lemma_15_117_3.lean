/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.Away.FiniteExtension.PrincipalQuotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.117.3 (0GLT)

Finite injective extensions that agree after inverting a nonzerodivisor admit compatible finite
lifts of sufficiently deep principal-power quotient isomorphisms.

@stack 0GLT
-/

/- Lemma 15.117.3: eventual finite lifting of principal-power quotient isomorphisms. -/
@[stacks 0GLT "Lemma 15.117.3"]
#check @Localization.Away.exists_finiteExtension_quotientIso

#check @principalIdeal
#check @principalPowerIdeal
#check @principalPowerIdealReductionMap
#check @Localization.awayMapₐ
