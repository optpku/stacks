/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Reduction
public import StacksCheckRecall.CommandCrossRef

/-!
# Remark 7.29.7 recall

The generic dense-subsite reduction of a morphism of topoi belongs to ReasLib.
This source file retains only the labeled textbook recall.
-/

@[expose] public section

/- Remark 7.29.7 (03CJ): a morphism of topoi admits a finite-limit,
subcanonical dense-subsite reduction that makes specified small families
representable. -/
@[stacks 03CJ] #check @CategoryTheory.MorphismOfTopoiIn.exists_reduction

#check @CategoryTheory.MorphismOfTopoiIn.Reduction.spec
