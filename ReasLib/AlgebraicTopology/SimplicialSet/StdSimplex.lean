/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017F

# Nondegenerate simplices of the standard simplex

This file records reusable source-independent consequences of the canonical standard-simplex
API.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.stdSimplex

namespace zeroObjEquiv

/-- The unique zero-simplex value has the canonical point as its coordinate. -/
@[stacks 017F "zero-simplex coordinate"]
def toFun {Delta : SimplexCategoryᵒᵖ} (_ : (Δ[0] : SSet.{u}).obj Delta) : PUnit.{u + 1} :=
  PUnit.unit

/-- The canonical point determines the constant simplex in every degree of `Δ[0]`. -/
@[stacks 017F "zero-simplex inverse coordinate"]
def invFun (Delta : SimplexCategoryᵒᵖ) (_ : PUnit.{u + 1}) :
    (Δ[0] : SSet.{u}).obj Delta :=
  const 0 0 Delta

/-- The constant zero-simplex is inverse to its point coordinate. -/
@[stacks 017F "zero-simplex coordinate left inverse"]
theorem left_inv (Delta : SimplexCategoryᵒᵖ)
    (x : (Δ[0] : SSet.{u}).obj Delta) :
    invFun Delta (toFun x) = x := sorry

/-- The point coordinate is inverse to the constant zero-simplex. -/
@[stacks 017F "zero-simplex coordinate right inverse"]
theorem right_inv (Delta : SimplexCategoryᵒᵖ) (x : PUnit.{u + 1}) :
    toFun (invFun Delta x) = x := sorry

end zeroObjEquiv

/-- Every degree of the zero simplex is canonically the one-point type. -/
@[stacks 017F "zero-simplex degree coordinates"]
def zeroObjEquiv (Delta : SimplexCategoryᵒᵖ) :
    (Δ[0] : SSet.{u}).obj Delta ≃ PUnit.{u + 1} where
  toFun := zeroObjEquiv.toFun
  invFun := zeroObjEquiv.invFun Delta
  left_inv := zeroObjEquiv.left_inv Delta
  right_inv := zeroObjEquiv.right_inv Delta

/-- The zero-simplex equivalence sends every simplex to the canonical point. -/
@[simp, stacks 017F "zero-simplex equivalence forward formula"]
theorem zeroObjEquiv.apply (Delta : SimplexCategoryᵒᵖ)
    (x : (Δ[0] : SSet.{u}).obj Delta) :
    zeroObjEquiv Delta x = zeroObjEquiv.toFun x := sorry

/-- The inverse zero-simplex equivalence sends the canonical point to the constant simplex. -/
@[simp, stacks 017F "zero-simplex equivalence inverse formula"]
theorem zeroObjEquiv.symm_apply (Delta : SimplexCategoryᵒᵖ) (x : PUnit.{u + 1}) :
    (zeroObjEquiv Delta).symm x = zeroObjEquiv.invFun Delta x := sorry

/-- The simplicial-set Yoneda equivalence evaluates a map from `Δ[n]` at the distinguished
top-dimensional simplex represented by `𝟙 ⦋n⦌`. -/
@[stacks 0177]
theorem _root_.SSet.yonedaEquiv_apply
    {U : SSet.{u}} {n : ℕ} (f : Δ[n] ⟶ U) :
    SSet.yonedaEquiv f =
      f.app (Opposite.op ⦋n⦌) (objEquiv.symm (𝟙 ⦋n⦌)) := sorry

/-- Example 14.11.2: the unique top-dimensional nondegenerate simplex of `Δ[n]` is the
identity simplex. -/
@[stacks 0176]
theorem nonDegenerate.eq_singleton_identity (n : ℕ) :
    (Δ[n] : SSet.{u}).nonDegenerate n =
      {objEquiv.symm (𝟙 ⦋n⦌)} := sorry

end SSet.stdSimplex
