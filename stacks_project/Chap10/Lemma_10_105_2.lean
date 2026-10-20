/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Catenary.Basic
import StacksCheckRecall

/-!
# Catenarity of the prime spectrum

@stack 02IH
-/

/- Lemma 10.105.2: a ring `R` is catenary if and only if its prime spectrum is a
catenary topological space. -/
@[stacks 02IH]
#check @isCatenaryRing_iff_catenarySpace_primeSpectrum
