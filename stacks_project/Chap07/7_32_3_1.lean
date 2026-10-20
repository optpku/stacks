/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.PresheafFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (fiber : C ⥤ Type w)

/- 7.32.3.1: for a functor u : C ⥤ Type and a set E, the presheaf u^p E is
defined by the object formula U ↦ Map(u(U), E). This is u.presheafCostalk:
(u.presheafCostalk.obj E).obj (op U) = (u.obj U → E). This defines a functor
u^p : Type ⥤ (Cᵒᵖ ⥤ Type). -/
@[stacks 04EI] #check (CategoryTheory.Functor.presheafCostalk fiber :
  Type w ⥤ (Cᵒᵖ ⥤ Type w))
