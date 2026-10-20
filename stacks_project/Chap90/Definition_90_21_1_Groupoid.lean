/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors

universe u v w

/- Groupoids in set-valued functors, with their existing public operations and laws. -/
#check (CategoryTheory.GroupoidInFunctors.{u, v, w} :
  (C : Type u) → [CategoryTheory.Category.{v} C] → Type (max u v (w + 1)))
