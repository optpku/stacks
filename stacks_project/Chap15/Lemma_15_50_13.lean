/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.FilteredColimit.GRing
import StacksCheckRecall

/-!
# Lemma 15.50.13

@stack 0A41
-/

@[expose] public section

/- Lemma 15.50.13: a henselian local ring is a filtered colimit of a directed system of
henselian local G-rings with local transition maps. -/
@[stacks 0A41]
#check @HenselianLocalRing.exists_filteredColimit_isGRing
