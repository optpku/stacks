/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Objects

/-!
# Degreewise object membership for formal coproducts

This leaf extends formal-coproduct object membership to simplicial formal coproducts without
introducing site or topology assumptions.
-/

@[expose] public section

universe w v u

namespace CategoryTheory
namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- A simplicial formal coproduct lies degreewise in `B` when every ordinary simplicial degree
has all component objects in `B`. -/
def degreewiseObjectsIn (K : SimplicialObject (FormalCoproduct.{w} C)) (B : Set C) : Prop :=
  ∀ n : ℕ, objectsIn (K.obj (Opposite.op <| SimplexCategory.mk n)) B

/-- Unfolding `degreewiseObjectsIn` quantifies over each ordinary simplicial degree. -/
@[simp] theorem degreewiseObjectsIn_iff
    (K : SimplicialObject (FormalCoproduct.{w} C)) (B : Set C) :
    degreewiseObjectsIn K B ↔
      ∀ n : ℕ, objectsIn (K.obj (Opposite.op <| SimplexCategory.mk n)) B := sorry

namespace DegreewiseObjectsIn

/-- A degreewise membership condition supplies the family membership condition in any chosen
simplicial degree. -/
theorem degree
    {K : SimplicialObject (FormalCoproduct.{w} C)} {B : Set C}
    (hK : degreewiseObjectsIn K B) (n : ℕ) :
    objectsIn (K.obj (Opposite.op <| SimplexCategory.mk n)) B := sorry

/-- Every component in a specified simplicial degree of a degreewise formal coproduct lies in the
chosen collection. -/
theorem mem
    {K : SimplicialObject (FormalCoproduct.{w} C)} {B : Set C}
    (hK : degreewiseObjectsIn K B) (n : ℕ)
    (i : (K.obj (Opposite.op <| SimplexCategory.mk n)).I) :
    (K.obj (Opposite.op <| SimplexCategory.mk n)).obj i ∈ B := sorry

end DegreewiseObjectsIn
end FormalCoproduct
end Limits
end CategoryTheory
