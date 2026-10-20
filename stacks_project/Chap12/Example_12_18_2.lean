/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Preadditive A] [Preadditive B] [Preadditive C]
variable (tensor : A ⥤ B ⥤ C) [tensor.Additive]
  [∀ X, (tensor.obj X).Additive]
variable (X : CochainComplex A ℤ) (Y : CochainComplex B ℤ)

/- Example 12.18.2 [0A5J]: applying a bifunctor that is additive in each variable to two
cochain complexes gives the canonical cohomological bicomplex. -/
@[stacks 0A5J]
#check (((tensor.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj X).obj Y :
  HomologicalComplex₂ C (up ℤ) (up ℤ))

/- Its terms and the differentials in both directions are available as computation lemmas. -/
#check @Functor.mapBifunctorHomologicalComplex_obj_obj_X_X
#check @Functor.mapBifunctorHomologicalComplex_obj_obj_d_f
#check @Functor.mapBifunctorHomologicalComplex_obj_obj_X_d
