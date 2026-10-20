/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Representability

universe u v

/- Representability of groupoids in functors by coyoneda presentations with an existing pushout. -/
#check (CategoryTheory.GroupoidInFunctors.IsRepresentable.{u, v} :
  {C : Type u} → [CategoryTheory.Category.{v} C] →
    CategoryTheory.GroupoidInFunctors.{u, v, v} C → Prop)
