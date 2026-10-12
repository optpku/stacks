/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.4

This file recalls the prime- and maximal-localization criterion for reflexive finite modules.

@stack 0AV1
-/

@[expose] public section

open Module

universe u v

/- Lemma 15.23.4: reflexivity of a finite module over a Noetherian domain can be checked at all
prime localizations or only at all maximal localizations. -/
@[stacks 0AV1 "Lemma 15.23.4"]
#check @Module.IsReflexive.localization_tfae

/- The canonical bridge identifying localized reflexivity with the localized evaluation map. -/
#check @Module.IsReflexive.atPrime_iff_bijective_eval
