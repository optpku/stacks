/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Semigroupal.Unit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SemigroupalCategory

universe v u

variable {C : Type u} [Category.{v} C] [SemigroupalCategory C]

/- Equation (0HAV). The triangle for an explicitly chosen unit of a coherent tensor.
The source's φ is the inverse associator (associator X unit.obj Y).inv. -/
@[stacks 0HAV] #check
  (CategoryTheory.SemigroupalCategory.triangle_stacks : ∀ (unit : Unit C) (X Y : C),
    (associator X unit.obj Y).inv ≫ whiskerRight (unit.rightUnitor.hom.app X) Y =
      whiskerLeft X (unit.leftUnitor.hom.app Y))
