/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Module.Support.Flat
import StacksCheckRecall

/-!
# Generalizations in the support of a flat module

@stack 080T
-/

@[expose] public section

/- Lemma 10.41.12: if `N` is a finite `S`-module that is flat over `R`, then
generalizations lift along the map `support S N → Spec R` induced by
`PrimeSpectrum.comap (algebraMap R S)`. -/
@[stacks 080T]
#check @Module.generalizingMap_support_comap_of_flat
