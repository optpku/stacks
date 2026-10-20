/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.29.1

The source-local comparison hypotheses and their direct-image equivalence are
generic site API owned by ReasLib. This file preserves the Stacks label as a
recall layer.
-/

@[expose] public section

/- Lemma 7.29.1 (03A0): a continuous and cocontinuous source-locally full,
source-locally faithful, cover-dense functor induces an equivalence through
its cocontinuous direct image on set-valued sheaves. -/
@[stacks 03A0 "faithfulness"] #check @CategoryTheory.Functor.IsSourceLocallyFaithful

@[stacks 03A0 "fullness"] #check @CategoryTheory.Functor.IsSourceLocallyFull

@[stacks 03A0 "comparison"] #check @CategoryTheory.Functor.directImage_isEquivalence

@[stacks 03A0 "special case"] #check @CategoryTheory.Functor.IsSpecialCocontinuous.directImage_isEquivalence
