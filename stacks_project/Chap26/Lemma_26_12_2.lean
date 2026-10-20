/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Reduced
import StacksCheckRecall

@[expose] public section

/- Lemma 26.12.2: a scheme is reduced exactly when every open section ring is reduced. -/
@[stacks 01J1] #check AlgebraicGeometry.Scheme.isReduced_iff
