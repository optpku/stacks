/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Total objects of graded objects

The total object of an `I`-graded object is the coproduct of its homogeneous pieces. This file
provides the shape-polymorphic additive owner; monoidal structure belongs in the higher
`Total.Monoidal` leaf.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.GradedObject.Total

variable {I : Type w} {C : Type u} [Category.{v} C]
variable [HasCoproductsOfShape I C]

/-- Totalization is Mathlib's canonical coproduct functor on a family. -/
@[stacks 01CF "total functor on graded objects"]
abbrev functor : GradedObject I C ⥤ C := Limits.Sigma.functor I

/-- Totalization sends a graded object to the coproduct of its homogeneous pieces. -/
@[simp]
theorem functor_obj (X : GradedObject I C) :
    (functor (I := I) (C := C)).obj X = ∐ X := rfl

/-- Totalization maps a graded morphism by the coproduct of its components. -/
@[simp]
theorem functor_map {X Y : GradedObject I C} (f : X ⟶ Y) :
    (functor (I := I) (C := C)).map f = Limits.Sigma.map f := rfl

end CategoryTheory.GradedObject.Total
