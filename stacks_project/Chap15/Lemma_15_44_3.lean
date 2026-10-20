/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.RegularLocal
import StacksCheckRecall

@[expose] public section

universe u v

/-!
# Lemma 15.44.3

@stack 0AH0

The reusable owner takes the canonical point `q : PrimeSpectrum B`; its contraction determines
the source localization, so no separate prime ideal or `[IsPrime]` witness is needed. This chapter
entry is only the source-label recall of that owner theorem.
-/

/- Lemma 15.44.3: regularity is equivalent on the two prime localizations of an etale map. -/
@[stacks 0AH0]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (q : PrimeSpectrum B) ↦
  (Algebra.Etale.localizationAtPrime_isRegularLocalRing_iff q :
    IsRegularLocalRing (Localization.AtPrime (q.asIdeal.under A)) ↔
      IsRegularLocalRing (Localization.AtPrime q.asIdeal))
