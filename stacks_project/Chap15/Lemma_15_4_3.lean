/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Filtration.ArtinRees.BaseChange

@[expose] public section

/-!
# Lemma 15.4.3 (07VG)

@stack 07VG
-/

-- Lemma 15.4.3: flat base change preserves the same Artin-Rees bound in the finite Noetherian
-- setup of the source.
@[stacks 07VG "Lemma 15.4.3"]
#check @LinearMap.IsArtinReesBound.baseChange_of_finite

-- Reusable generalized owner, with the inessential finiteness hypotheses removed.
#check @LinearMap.IsArtinReesBound.baseChange
