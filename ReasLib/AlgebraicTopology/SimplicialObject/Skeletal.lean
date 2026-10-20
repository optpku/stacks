/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Skeletal simplicial objects

A simplicial object is `n`-skeletal when it is the left Kan extension of its restriction to
degrees at most `n`.  This intrinsic formulation does not require a chosen skeleton functor in
the ambient category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace Truncated

/-- The identity exhibits a simplicial object as a left extension of its truncation. -/
@[stacks 018N "identity left extension of a truncated simplicial object"]
def leftExtensionInclusion (X : SimplicialObject C) (n : ℕ) :
    Functor.LeftExtension (SimplexCategory.Truncated.inclusion n).op
      ((SimplexCategory.Truncated.inclusion n).op ⋙ X) :=
  Functor.LeftExtension.mk _ (𝟙 _)

end Truncated

/-- A simplicial object is `n`-skeletal when it is the left Kan extension of its restriction to
degrees at most `n` via the identity transformation. -/
@[mk_iff]
class IsSkeletal (X : SimplicialObject C) (n : ℕ) : Prop where
  isLeftKanExtension :
    X.IsLeftKanExtension
      (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X))

attribute [instance] IsSkeletal.isLeftKanExtension

namespace IsSkeletal

/-- The identity left extension of an `n`-skeletal object is universal. -/
noncomputable def isUniversal (X : SimplicialObject C) (n : ℕ) [X.IsSkeletal n] :
    (Truncated.leftExtensionInclusion X n).IsUniversal :=
  X.isUniversalOfIsLeftKanExtension
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X))

namespace truncation

/-- Maps from an `n`-skeletal simplicial object are classified by maps between the
`n`-truncations. -/
noncomputable def homEquiv (X : SimplicialObject C) (n : ℕ) [X.IsSkeletal n]
    (V : SimplicialObject C) :
    (X ⟶ V) ≃ ((SimplicialObject.truncation n).obj X ⟶
      (SimplicialObject.truncation n).obj V) :=
  X.homEquivOfIsLeftKanExtension
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X)) V

/-- The forward map of `IsSkeletal.truncation.homEquiv` is restriction to degrees at most
`n`. -/
@[simp]
theorem homEquiv.apply (X : SimplicialObject C) (n : ℕ) [X.IsSkeletal n]
    (V : SimplicialObject C) (f : X ⟶ V) :
    homEquiv X n V f = (SimplicialObject.truncation n).map f := sorry

/-- Restriction to degree at most `n` is a bijection on maps from an `n`-skeletal source. -/
theorem map_bijective (X : SimplicialObject C) (n : ℕ) [X.IsSkeletal n]
    (V : SimplicialObject C) :
    Function.Bijective
      (fun f : X ⟶ V ↦ (SimplicialObject.truncation n).map f) := sorry

/-- Maps from an `n`-skeletal source are equal when their `n`-truncations are equal. -/
theorem hom_ext (X : SimplicialObject C) (n : ℕ) [X.IsSkeletal n]
    {V : SimplicialObject C} {f g : X ⟶ V}
    (h : (SimplicialObject.truncation n).map f =
      (SimplicialObject.truncation n).map g) :
    f = g := sorry

end truncation

/-- Skeletality is invariant under isomorphism. -/
theorem ofIso {X Y : SimplicialObject C} {n : ℕ}
    [X.IsSkeletal n] (e : X ≅ Y) : Y.IsSkeletal n := sorry

/-- Explicit-proof form of invariance of skeletality under isomorphism. -/
theorem ofIso.explicit {X Y : SimplicialObject C} {n : ℕ}
    (hX : X.IsSkeletal n) (e : X ≅ Y) : Y.IsSkeletal n := sorry

end IsSkeletal

end CategoryTheory.SimplicialObject
