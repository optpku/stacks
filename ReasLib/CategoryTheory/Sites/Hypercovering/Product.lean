/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Binary products of hypercoverings

This leaf owns the binary-product stability construction for topology-relative
formal-coproduct hypercoverings.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open Limits
open SemiRepresentableFamily.OverFamily
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Hypercovering

variable [HasPullbacks C]
variable {X : C}

/-- The degree-zero family of the product of two hypercoverings is covering. -/
theorem prod_zero_isCovering
    (K L : Hypercovering J X) :
    ((K.toSimplicialObject ⨯ L.toSimplicialObject).obj
      (op <| SimplexCategory.mk 0)).toSieve ∈ J X := sorry

/-- Every higher matching map of the product of two hypercoverings is covering. -/
theorem prod_succ_isCovering
    (K L : Hypercovering J X) (n : ℕ) :
    SemiRepresentableFamily.OverFamily.covering J
      (SimplicialObject.matchingMap (K.toSimplicialObject ⨯ L.toSimplicialObject) n) := sorry

/-- The binary product of two hypercoverings of the same target. -/
@[stacks 01GI "binary product of hypercoverings"]
noncomputable def prod (K L : Hypercovering J X) : Hypercovering J X where
  toSimplicialObject := K.toSimplicialObject ⨯ L.toSimplicialObject
  zero_isCovering := prod_zero_isCovering K L
  succ_isCovering := prod_succ_isCovering K L

/-- The simplicial object underlying the binary product hypercovering is the categorical product
of the underlying simplicial objects. -/
@[simp]
theorem prod_toSimplicialObject (K L : Hypercovering J X) :
    (prod K L).toSimplicialObject = (K.toSimplicialObject ⨯ L.toSimplicialObject) := sorry

end Hypercovering

end CategoryTheory
