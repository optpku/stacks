/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty.Sections
import StacksCheckRecall

universe u v w

open CategoryTheory CategoryTheory.Limits

/- Remark 59.11.2 (1): for the empty covering with index `I = ∅`, the value
   `𝓕(∅)` is an empty product and hence a final object in the corresponding category. -/
@[stacks 03NM]
#check (CategoryTheory.GrothendieckTopology.IsSheafTheoreticallyEmpty.isTerminal_app :
  ∀ {C : Type u} [Category.{v} C] {A : Type w} [Category A]
    {J : GrothendieckTopology C} {U : C},
    J.IsSheafTheoreticallyEmpty U → (F : Sheaf J A) →
      IsTerminal (F.obj.obj (Opposite.op U)))

/- Remark 59.11.2 (2): in `Sets`, the empty product is a singleton. -/
@[stacks 03NM]
#check (CategoryTheory.GrothendieckTopology.IsSheafTheoreticallyEmpty.uniqueSections :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C},
    J.IsSheafTheoreticallyEmpty U → (F : Sheaf J (Type w)) →
      Nonempty (Unique (F.obj.obj (Opposite.op U))))

/- Remark 59.11.2 (3): in `Ab`, the empty product is a singleton. -/
@[stacks 03NM]
#check (CategoryTheory.GrothendieckTopology.IsSheafTheoreticallyEmpty.uniqueAddCommGrpSections :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C},
    J.IsSheafTheoreticallyEmpty U →
      (F : Sheaf J AddCommGrpCat.{w}) →
        Nonempty (Unique (F.obj.obj (Opposite.op U))))
