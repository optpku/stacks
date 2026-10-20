/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Basic

@[expose] public section

namespace Order

/-- The source type of a function, equipped with order transported from its target. -/
def Induced {α β : Type*} (f : α → β) := α

namespace Induced

variable {α β : Type*} {f : α → β}

/-- Regard an element as an element of the type carrying the induced order. -/
def of (f : α → β) (a : α) : Induced f := a

/-- Recover the underlying element of a type carrying an induced order. -/
def val (a : Induced f) : α := a

/-- The preorder induced by a function into a preordered type. -/
instance instPreorder [Preorder β] : Preorder (Induced f) :=
  Preorder.lift (fun a ↦ f (val a))

/-- An induced inequality is precisely the inequality of the images. -/
theorem le_iff [Preorder β] (a b : Induced f) :
    a ≤ b ↔ f (val a) ≤ f (val b) := Iff.rfl

end Induced
end Order
