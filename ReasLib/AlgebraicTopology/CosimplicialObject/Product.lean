/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Product

/-!
@stack 016Z

# Pointwise products of cosimplicial objects

This file exposes the canonical functor-category pointwise product instance through Mathlib's
opaque `CosimplicialObject` wrapper.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
/-- The generic pointwise construction supplies the canonical binary product of two
cosimplicial objects. -/
@[stacks 016Z "pointwise binary product of cosimplicial objects"]
public noncomputable instance (priority := low) pointwise.binaryProduct
    (U V : CosimplicialObject C)
    [h_pointwise : Limits.FunctorCategory.Binary.HasPointwiseProduct U V] :
    HasBinaryProduct U V :=
  (functorCategoryHasLimit
    (pair (U : SimplexCategory ⥤ C) (V : SimplexCategory ⥤ C)) :
      HasBinaryProduct (U : SimplexCategory ⥤ C) (V : SimplexCategory ⥤ C))

end CategoryTheory.CosimplicialObject
