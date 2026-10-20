/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.FilteredColimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.37.17

@stack 037D
-/

/- Lemma 10.37.17 (Stacks tag `037D`): normality of a filtered colimit is
owned by the shared cocone-level normality API. -/
@[stacks 037D]
#check @IsNormalRing.of_isColimit_filtered

@[stacks 037D "underlying filtered colimit criterion"]
#check @IsNormalRing.of_isColimit_under_filtered
