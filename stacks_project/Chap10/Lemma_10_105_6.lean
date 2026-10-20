/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Catenary.Local
import StacksCheckRecall

/-!
# Lemma 10.105.6

The prime-local and maximal-local catenarity criteria are shared infrastructure
in `ReasLib.RingTheory.Catenary.Local`.

@stack 0AUN
-/

/- Lemma 10.105.6 (1): catenarity can be checked after localization at every
prime, or only at every maximal ideal. -/
@[stacks 0AUN "(1), catenary localization criteria"]
#check @isCatenaryRing_localization_tfae

#check @isCatenaryRing_iff_forall_localizationAtPrime
#check @isCatenaryRing_iff_forall_localizationAtMaximal

/- Lemma 10.105.6 (2): for a Noetherian ring, universal catenarity can be
checked after localization at every prime, or only at every maximal ideal. -/
@[stacks 0AUN "(2), universal-catenarity localization criteria"]
#check @universallyCatenaryRing_localization_tfae

#check @universallyCatenaryRing_iff_forall_localizationAtPrime
#check @universallyCatenaryRing_iff_forall_localizationAtMaximal
