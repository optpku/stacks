/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Dense subsites on slice sites

This leaf owns the stability of a dense subsite under passage to an over
category.  It is independent of any particular comparison-lemma application.
-/

@[expose] public section

universe uC uD vC vD

namespace CategoryTheory

namespace Functor

namespace IsDenseSubsite

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Lemma 7.29.3: a dense subsite remains dense after passing to the slice
sites over an object and its image. -/
@[stacks 03CH]
instance overPost
    (F : C ⥤ D) (X : C) [F.IsDenseSubsite J K] :
    (Over.post F).IsDenseSubsite (J.over X) (K.over (F.obj X)) := sorry

end IsDenseSubsite

end Functor

end CategoryTheory
