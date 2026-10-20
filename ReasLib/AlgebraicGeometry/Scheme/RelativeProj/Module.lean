/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.GradedObject
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The relative-Proj module obtained in degree zero from a pulled-back graded module,
its pulled-back graded algebra, and the integral tensor powers of an invertible module. -/
noncomputable def relativeProjTilde
    {Y T : Scheme.{u}} (f : T ⟶ Y)
    (𝒜d ℳd : CategoryTheory.GradedObject ℤ Y.Modules)
    (ℒ : T.Modules) [Invertible ℒ]
    (relativeTensorOver :
      CategoryTheory.GradedObject ℤ T.Modules →
        CategoryTheory.GradedObject ℤ T.Modules →
        CategoryTheory.GradedObject ℤ T.Modules →
        CategoryTheory.GradedObject ℤ T.Modules) : T.Modules :=
  (CategoryTheory.GradedObject.eval (0 : ℤ)).obj
    (relativeTensorOver
      (fun n => (pullback f).obj (ℳd n))
      (fun n => (pullback f).obj (𝒜d n))
      (fun n => tensorPowerInt ℒ n))

/-- The defining degree-zero relative-tensor formula for `relativeProjTilde`. -/
theorem relativeProjTilde_def
    {Y T : Scheme.{u}} (f : T ⟶ Y)
    (𝒜d ℳd : CategoryTheory.GradedObject ℤ Y.Modules)
    (ℒ : T.Modules) [Invertible ℒ]
    (relativeTensorOver :
      CategoryTheory.GradedObject ℤ T.Modules →
        CategoryTheory.GradedObject ℤ T.Modules →
        CategoryTheory.GradedObject ℤ T.Modules →
        CategoryTheory.GradedObject ℤ T.Modules) :
    relativeProjTilde f 𝒜d ℳd ℒ relativeTensorOver =
      (CategoryTheory.GradedObject.eval (0 : ℤ)).obj
        (relativeTensorOver
          (fun n => (pullback f).obj (ℳd n))
          (fun n => (pullback f).obj (𝒜d n))
          (fun n => tensorPowerInt ℒ n)) := sorry

end AlgebraicGeometry.Scheme.Modules
