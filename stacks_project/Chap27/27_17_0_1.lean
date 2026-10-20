/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Module
import StacksCheckRecall

@[expose] public section

/- 27.17.0.1
For `f : T ⟶ Y`, the module `widetildeℳ_T` is the degree-zero component of the
relative tensor product of `f^*ℳd` over `f^*𝒜d` with `n ↦ ℒ^{⊗ n}`.
-/
@[stacks 01O6] #check (AlgebraicGeometry.Scheme.Modules.relativeProjTilde_def :
    ∀ {Y T : AlgebraicGeometry.Scheme} (f : T ⟶ Y)
      (𝒜d ℳd : CategoryTheory.GradedObject ℤ Y.Modules)
      (ℒ : T.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (relativeTensorOver :
        CategoryTheory.GradedObject ℤ T.Modules →
          CategoryTheory.GradedObject ℤ T.Modules →
          CategoryTheory.GradedObject ℤ T.Modules →
          CategoryTheory.GradedObject ℤ T.Modules),
      AlgebraicGeometry.Scheme.Modules.relativeProjTilde
          f 𝒜d ℳd ℒ relativeTensorOver =
        (CategoryTheory.GradedObject.eval (0 : ℤ)).obj
          (relativeTensorOver
            (fun n => (AlgebraicGeometry.Scheme.Modules.pullback f).obj (ℳd n))
            (fun n => (AlgebraicGeometry.Scheme.Modules.pullback f).obj (𝒜d n))
            (fun n => AlgebraicGeometry.Scheme.Modules.tensorPowerInt ℒ n)))

#check (AlgebraicGeometry.Scheme.Modules.relativeProjTilde :
    ∀ {Y T : AlgebraicGeometry.Scheme} (f : T ⟶ Y)
      (𝒜d ℳd : CategoryTheory.GradedObject ℤ Y.Modules)
      (ℒ : T.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (relativeTensorOver :
        CategoryTheory.GradedObject ℤ T.Modules →
          CategoryTheory.GradedObject ℤ T.Modules →
          CategoryTheory.GradedObject ℤ T.Modules →
          CategoryTheory.GradedObject ℤ T.Modules),
      T.Modules)
