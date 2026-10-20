/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.TensorProduct
import StacksCheckRecall

open Algebra.CotangentComplex CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u

/- 92.15.0.1: the canonical cotangent transitivity triangles through the two
factors of a tensor product form the middle row and column of a commuting
diagram. The cone of the sum of their first maps completes both outer lines
to distinguished triangles. -/
@[stacks 09D9] #check (Algebra.CotangentComplex.tensorProductDiagram :
  ∀ (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B],
    tensorProductMiddleRow R A B ∈
      distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) ∧
    tensorProductMiddleColumn R A B ∈
      distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) ∧
    tensorProductTopMap R A B =
      (tensorProductMiddleRow R A B).mor₁ ≫ (tensorProductMiddleColumn R A B).mor₂ ∧
    tensorProductRightMap R A B =
      (tensorProductMiddleColumn R A B).mor₁ ≫ (tensorProductMiddleRow R A B).mor₂ ∧
    (tensorProductMiddleColumn R A B).mor₂ ≫ tensorProductFromOverB R A B =
      tensorProductConeInr R A B ∧
    (tensorProductMiddleRow R A B).mor₂ ≫ tensorProductFromOverA R A B =
      tensorProductConeInr R A B ∧
    ∃ (δTop : tensorProductCone R A B ⟶
        (DerivedCategory.Q.obj (tensorProductExtendLeft R A B))⟦(1 : ℤ)⟧)
      (δRight : tensorProductCone R A B ⟶
        (DerivedCategory.Q.obj (tensorProductExtendRight R A B))⟦(1 : ℤ)⟧),
      Triangle.mk (tensorProductTopMap R A B) (tensorProductFromOverB R A B) δTop ∈
        distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))) ∧
      Triangle.mk (tensorProductRightMap R A B) (tensorProductFromOverA R A B) δRight ∈
        distTriang (DerivedCategory (ModuleCat.{u} (A ⊗[R] B))))
