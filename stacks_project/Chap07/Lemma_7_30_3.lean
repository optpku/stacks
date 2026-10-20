/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

-- Category-of-elements localization is a reusable site-theoretic construction.
public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
import StacksCheckRecall

@[expose] public section

/- Lemma 7.30.3 (0791): for a sheaf `F`, the opposite category of elements carries the
localization topology; its projection is continuous and cocontinuous, and its sheaf category is
equivalent to `Over F`. The reusable construction is owned by ReasLib. -/
@[stacks 0791 "(1)"] #check @CategoryTheory.localizationProjection_isContinuous

@[stacks 0791 "(2)"] #check @CategoryTheory.localizationProjection_isCocontinuous

@[stacks 0791 "(3)"] #check @CategoryTheory.sheafCategoryOfElementsEquivOver

@[stacks 0791 "(4)"] #check @CategoryTheory.localizationMorphismOfTopoiIn
