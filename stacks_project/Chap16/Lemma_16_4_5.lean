/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.NeronBlowup.Termination

@[expose] public section

/- Lemma 16.4.5 (tag 0BJ6): the deterministic iterated-blowup theorem and its
torsion-length descent infrastructure are provided by ReasLib. -/

@[stacks 0BJ6]
#check @Algebra.DVR.Factorization.NeronBlowup.exists_smooth_iterate

@[stacks 0BJ6]
#check @Algebra.DVR.Factorization.CenteredSmoothPresentation.defect

@[stacks 0BJ6]
#check @Algebra.DVR.Factorization.NeronBlowup.exists_defect_lt

@[stacks 0BJ6]
#check @Algebra.DVR.Factorization.CenteredSmoothPresentation.of

@[stacks 0BJ6]
#check @Algebra.DVR.Factorization.CenteredSmoothPresentation.coe_defect

@[stacks 0BJ6]
#check @Module.natLength
