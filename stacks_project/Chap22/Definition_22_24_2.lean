/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u v' u'

variable (R : Type w) [Semiring R]
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable [Preadditive C] [Preadditive D]
variable [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
variable (F : C ⥤ D)

/- Definition 22.24.2 (09MK): an `R`-linear functor is canonically represented by
`CategoryTheory.Functor.Linear R F`. -/
@[stacks 09MK] #check (CategoryTheory.Functor.Linear R F : Prop)

/- It suffices to test `R`-linearity on scalar multiples of identity morphisms. -/
#check (CategoryTheory.Functor.linear_iff R F :
  CategoryTheory.Functor.Linear R F ↔
    ∀ (X : C) (r : R), F.map (r • 𝟙 X) = r • 𝟙 (F.obj X))
