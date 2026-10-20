/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Functor.KanExtension.Representable

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 7.5.6 (04D2): the left Kan extension of a representable presheaf
along `u.op` is represented by the image of its representing object. -/
@[stacks 04D2] #check @CategoryTheory.Functor.LeftKanExtension.Representable.iso
