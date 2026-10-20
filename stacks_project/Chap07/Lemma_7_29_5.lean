/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Family
import StacksCheckRecall

/-!
# Lemma 7.29.5

The reusable dense-subsite presentation of a small family of sheaves is
owned by ReasLib. This file retains the source label as a thin recall.
-/

@[expose] public section

/- Lemma 7.29.5 (03CI): every small family of set-valued sheaves on a site
admits a finite-limit subcanonical dense-subsite presentation in which the
family is representable; the source cover, subobject, and full-faithfulness
properties are retained by the presentation API. -/
@[stacks 03CI] #check @CategoryTheory.Functor.DenseSubsite.Family.Presentation.nonempty

/- Companion APIs expose the dense comparison, sheaf transport, and complete
source-facing specification of a chosen presentation. -/
#check @CategoryTheory.Functor.DenseSubsite.Family.Presentation.specialCocontinuous
#check @CategoryTheory.Functor.DenseSubsite.Family.Presentation.transport
#check @CategoryTheory.Functor.DenseSubsite.Family.Presentation.familyIsRepresentable
#check @CategoryTheory.Functor.DenseSubsite.Family.Presentation.spec
#check @CategoryTheory.Functor.DenseSubsite.Family.Presentation.fullyFaithful
