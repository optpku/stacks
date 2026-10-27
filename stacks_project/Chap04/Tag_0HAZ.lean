/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Semigroupal.Commutativity
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SemigroupalCategory

universe u v

/- Equation (0HAZ). A natural involutive commutativity constraint is compatible
with the associator precisely when the displayed hexagon commutes for all objects.
The source's φ is `associator.inv`; its vertical and lower-right ψ arrows are
`whiskerLeft X (ψ.braiding Y Z).hom` and `whiskerRight (ψ.braiding X Z).hom Y`.
No tensor unit is assumed. -/
@[stacks 0HAZ] #check
  (CategoryTheory.SemigroupalCategory.CommutativityConstraint.isCompatible_iff :
    ∀ {C : Type u} [Category.{v} C] [SemigroupalCategory C]
      (ψ : CommutativityConstraint C),
    ψ.IsCompatible ↔ ∀ X Y Z : C,
      (associator X Y Z).inv ≫ (ψ.braiding (tensorObj X Y) Z).hom ≫
          (associator Z X Y).inv =
        whiskerLeft X (ψ.braiding Y Z).hom ≫ (associator X Z Y).inv ≫
          whiskerRight (ψ.braiding X Z).hom Y)
