/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent
public import ReasLib.CategoryTheory.Limits.CoproductToProduct

/-!
# Coproducts and products of shifted sheaves on algebraic stacks
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicStack GroupoidsOver
open Limits

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The family of derived objects obtained by placing `F n` in cohomological
degree `-n`, representing the shifted sheaves `F n[n]`. -/
noncomputable abbrev shiftSingle {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : ℕ → fppfModules X) (n : ℕ) : ModuleDerived X :=
  (DerivedCategory.singleFunctor (fppfModules X) (-(n : ℤ))).obj (F n)

/-- For locally quasi-coherent fppf module sheaves with flat base change on an
algebraic stack, the canonical comparison from the coproduct of `F n[n]` to
their product is an isomorphism in `D(𝒪_X)`. -/
theorem shiftSingle_coproductToProduct_isIso {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (F : ℕ → fppfModules X)
    (hF : ∀ n, FppfModules.lqcohFbc X (F n))
    [HasCoproduct (shiftSingle F)] [HasProduct (shiftSingle F)] :
    IsIso (coproductToProduct (shiftSingle F)) := sorry

end AlgebraicGeometry.AlgebraicStack
