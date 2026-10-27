/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Semigroupal.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory SemigroupalCategory

universe v u

variable {C : Type u} [Category.{v} C] [SemigroupalCategory C]

/- Equation (0HAU): the pentagon commutes for the source associativity constraint
`φ X Y Z = (associator X Y Z).inv`, with no chosen unit object. -/
@[stacks 0HAU] #check (CategoryTheory.SemigroupalCategory.pentagon_inv : ∀ (X Y Z W : C),
    whiskerLeft X (associator Y Z W).inv ≫
        (associator X (tensorObj Y Z) W).inv ≫ whiskerRight (associator X Y Z).inv W =
      (associator X Y (tensorObj Z W)).inv ≫ (associator (tensorObj X Y) Z W).inv)
