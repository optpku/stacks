/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.Geometric.Reduced
import StacksCheckRecall

/-!
# Lemma 15.51.9

@stack 0BIW
-/

@[expose] public section

/- Lemma 15.51.9: geometric reducedness satisfies the five formal-fiber permanence laws. -/
@[stacks 0BIW "geometrically reduced formal-fiber laws"]
#check @FieldAlgebraProperty.geometricallyReduced.formalFiberLaws
