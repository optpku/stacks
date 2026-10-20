/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Retraction

@[expose] public section

/- Lemma 16.3.1: a finitely presented algebra admits a finite type smoothing
retraction with the stated localized cotangent properties. -/
@[stacks 07CE]
#check @Algebra.RetractExtension.Smoothing.nonempty

#check @Algebra.RetractExtension.Smoothing
#check @Algebra.FreeCotangentGenerators
#check @Algebra.FreeCotangentGenerators.spec
#check @Algebra.RetractExtension.Smoothing.spec
#check @Algebra.RetractExtension.retract
