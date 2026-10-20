/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.IntermediateField.Algebraic
import StacksCheckRecall

@[expose] public section

/- Lemma 9.8.6 (Tag 09GH): adjoining a finite family of algebraic elements to a field is a
finite-dimensional extension. -/
@[stacks 09GH]
#check FieldExtension.finiteDimensionalAdjoinRangeOfIsAlgebraic
