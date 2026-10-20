/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.QuasiRegular.Cotangent

/-!
Lemma 15.32.3 (08RK): the cotangent module of a quasi-regular ideal is finite projective;
the reusable owner is `Ideal.IsQuasiRegularIdeal.cotangent_finiteProjective`.
@stack 08RK
-/

@[expose] public section

/- Lemma 15.32.3, tag 08RK: the cotangent module of a quasi-regular ideal is finite projective. -/
@[stacks 08RK "quasi-regular ideal cotangent module"]
#check @Ideal.IsQuasiRegularIdeal.cotangent_finiteProjective
