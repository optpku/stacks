/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.Representability
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 90.21.4: a groupoid in functors on `C` is representable if it is
isomorphic to a coyoneda form `(coyoneda.obj (op U), coyoneda.obj (op R), s, t, c)`
for objects `U`, `R` of `C` such that the pushout `R ⨿_{s, U, t} R` exists. -/
@[stacks 06K6]
#check (CategoryTheory.GroupoidInFunctors.IsRepresentable.{u, v} :
  {C : Type u} → [CategoryTheory.Category.{v} C] →
    CategoryTheory.GroupoidInFunctors.{u, v, v} C → Prop)
