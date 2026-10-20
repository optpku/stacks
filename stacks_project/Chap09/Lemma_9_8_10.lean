/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.IntermediateField.Algebraic
import StacksCheckRecall

@[expose] public section

/- Lemma 9.8.10 (Tag 0BID): a subring of an algebraic field extension that contains the base
field is a field. -/
@[stacks 0BID]
#check Subring.isFieldOfAlgebraic
