/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Projective.Ext
import StacksCheckRecall

/-!
# Lemma 10.77.3

Projectivity of a finite module over a Noetherian ring is recalled from its
degree-one `Ext` criterion in `ReasLib`.

@stack 0G8T
-/

@[expose] public section

-- Lemma 10.77.3: a finite module is projective when `Ext¹` against every finite module vanishes.
@[stacks 0G8T]
#check @Module.Projective.of_ext_one_vanishing_on_finite
