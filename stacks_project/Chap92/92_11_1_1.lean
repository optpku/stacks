/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Comparison
public import stacks_project.Chap92.«92_11_1_1_Comparison»
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CommRingCat.Under.FreeAlgebra

noncomputable section

universe u


/- 92.11.1.1: The canonical comparison from the kernel-to-differentials complex of a
polynomial presentation to the cotangent complex in the derived category of A-modules. -/
@[stacks 08R8] #check
  (CategoryTheory.CommRingCat.Under.CotangentComplex.Comparison.comparisonDerived :
    ∀ (A : CommRingCat.{u}) (B : Under A) (E : Type u)
      (φ : (functor A).obj E ⟶ B),
      DerivedCategory.Q.obj
        (CategoryTheory.CommRingCat.Under.CotangentComplex.Comparison.kernelDifferentialsComplex
          A B E φ) ⟶
        DerivedCategory.Q.obj
          (CategoryTheory.CommRingCat.Under.CotangentComplex.Comparison.objRestrictScalars A B))
