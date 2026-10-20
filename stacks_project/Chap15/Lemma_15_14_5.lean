/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed.IntegrallyClosed

@[expose] public section

/- Lemma 15.14.5: a normal domain is absolutely integrally closed exactly when
its canonical fraction field is algebraically closed. -/
/-!
@stack 0DCQ
-/
@[stacks 0DCQ "Lemma 15.14.5"]
#check @IsAbsolutelyIntegrallyClosed.iff_isAlgClosed_fractionRing

/- The reusable owner also supports any chosen fraction-field model. -/
#check @IsAbsolutelyIntegrallyClosed.iff_isAlgClosed_of_isFractionRing
