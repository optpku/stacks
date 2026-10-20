/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Normal.Embeddings
import StacksCheckRecall

@[expose] public section

/- Lemma 9.15.5 (Tag 09HQ): an algebraic extension is normal exactly when every pair of
embeddings into `AlgebraicClosure F` has the same image intermediate field. -/
@[stacks 09HQ]
#check FieldExtension.normal_iff_forall_algHom_fieldRange_eq
