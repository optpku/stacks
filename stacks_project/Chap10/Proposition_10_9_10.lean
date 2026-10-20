/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.Iterated
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.9.10

@stack 02C6
-/

/- The generic iterated-localization predicate and uniqueness equivalence are the canonical
infrastructure behind the source-facing supremum model above. -/
#check @IsLocalization.localizationLocalizationSubmodule
#check @IsLocalization.localization_localization_isLocalization
#check @IsLocalization.algEquiv

@[stacks 02C6 "iterated localization equivalence"]
#check @Localization.supEquivIterated

@[stacks 02C6 "iterated localization equivalence on scalars"]
#check @Localization.supEquivIterated_apply_algebraMap

@[stacks 02C6 "iterated localization equivalence on fractions"]
#check @Localization.supEquivIterated_mk

end
