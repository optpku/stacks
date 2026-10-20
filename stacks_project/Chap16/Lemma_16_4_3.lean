/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.NeronBlowup.Differentials

@[expose] public section

/- Lemma 16.4.3 (1) (tag 0BJ4): one affine Neron blowup preserves smoothness at the closed
center under the separable residue-field hypothesis. -/
@[stacks 0BJ4]
#check @Algebra.DVR.Factorization.NeronBlowup.smoothAtClosedCenter

/- Lemma 16.4.3 (2) (tag 0BJ4): the localized Kähler map is the left arrow of the asserted
short exact sequence, with cokernel rank equal to the dimension of the old local special fiber. -/
@[stacks 0BJ4]
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.Sequence.nonempty

#check @Algebra.DVR.Factorization.NeronBlowup.Differential.map
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.map_tmul
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.Sequence
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.Sequence.of
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.Sequence.spec
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.Sequence.shortComplex
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.Sequence.shortExact
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.SourceSpecialFiber
#check @Algebra.DVR.Factorization.NeronBlowup.Differential.TargetSpecialFiber
