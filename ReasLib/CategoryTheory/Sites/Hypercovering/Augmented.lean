/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.FiniteLimits
public import ReasLib.CategoryTheory.MorphismProperty.Hypercovering
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Singleton
public import ReasLib.CategoryTheory.Sites.Hypercovering.Constructors
public import ReasLib.CategoryTheory.Sites.MorphismProperty.Covering
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hypercoverings from augmented simplicial objects

An augmented simplicial object first defines a simplicial object in a slice category.  Its
relative matching maps give the topology-independent owner of the source conditions; applying the
singleton-family inclusion then compares this owner with site-theoretic hypercoverings.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.Augmented

open Opposite Limits
open scoped CategoryTheory.SemiRepresentableFamily Simplicial

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C}

/-- The relative degree-`n + 1` matching map, expressed in the ambient category by forgetting
the slice structure. -/
abbrev relativeMatchingMap (A : SimplicialObject.Augmented C) (n : ℕ) :
    A.left.obj (op <| SimplexCategory.mk (n + 1)) ⟶
      ((SimplicialObject.cosk n).obj A.toOver).obj
        (op <| SimplexCategory.mk (n + 1)) |>.left :=
  (SimplicialObject.matchingMap A.toOver n).left

/-- The degree-zero singleton family associated to an augmented simplicial object. -/
abbrev zeroFamily (A : SimplicialObject.Augmented C) :
    SemiRepresentableFamily.OverFamily.{v, u, w} A.right :=
  SemiRepresentableFamily.OverFamily.singleton A.zeroMap

/-- The degree-one singleton family over `A.left.obj [0] ×_{A.right} A.left.obj [0]`. -/
abbrev oneFamily (A : SimplicialObject.Augmented C) :
    SemiRepresentableFamily.OverFamily.{v, u, w} (pullback A.zeroMap A.zeroMap) :=
  SemiRepresentableFamily.OverFamily.singleton A.oneMap

/-- The singleton family associated to the positive-degree relative matching map. -/
abbrev higherFamily (A : SimplicialObject.Augmented C) (n : ℕ) :
    SemiRepresentableFamily.OverFamily.{v, u, w}
      (((SimplicialObject.cosk n).obj A.toOver).obj
        (op <| SimplexCategory.mk (n + 1))).left :=
  SemiRepresentableFamily.OverFamily.singleton (A.relativeMatchingMap n)

/-- The source-facing hypercovering condition on an augmented simplicial object: its augmentation
and all relative matching maps are singleton covering arrows. -/
@[stacks 0GM9 "hypercovering condition for an augmented simplicial object"]
abbrev IsHypercovering (J : GrothendieckTopology C)
    (A : SimplicialObject.Augmented C) : Prop :=
  MorphismProperty.Hypercovering J.coveringArrows A.toOver

namespace IsHypercovering

/-- The degree-zero singleton family of an augmented hypercovering is covering. -/
theorem zero {A : SimplicialObject.Augmented C} (hA : A.IsHypercovering J) :
    A.zeroFamily.toSieve ∈ J A.right := sorry

/-- The degree-one singleton family of an augmented hypercovering is covering. -/
theorem one {A : SimplicialObject.Augmented C} (hA : A.IsHypercovering J) :
    A.oneFamily.toSieve ∈ J (pullback A.zeroMap A.zeroMap) := sorry

/-- Every successor-level relative matching family of an augmented hypercovering is covering. -/
theorem higher {A : SimplicialObject.Augmented C} (hA : A.IsHypercovering J) (n : ℕ) :
    (A.higherFamily (n + 1)).toSieve ∈
      J (((SimplicialObject.cosk (n + 1)).obj A.toOver).obj
        (op <| SimplexCategory.mk (n + 2))).left := sorry

/-- The three source-facing covering conditions imply the relative hypercovering condition. -/
theorem of_zero_one_higher {A : SimplicialObject.Augmented C}
    (h_zero : A.zeroFamily.toSieve ∈ J A.right)
    (h_one : A.oneFamily.toSieve ∈ J (pullback A.zeroMap A.zeroMap))
    (h_higher : ∀ n : ℕ,
      (A.higherFamily (n + 1)).toSieve ∈
        J (((SimplicialObject.cosk (n + 1)).obj A.toOver).obj
          (op <| SimplexCategory.mk (n + 2))).left) :
    A.IsHypercovering J := sorry

end IsHypercovering

/-- The degree-zero term of the singleton-family lift is covering whenever the augmented object
satisfies its relative hypercovering condition. -/
theorem toOverFamily_zero_isCovering (A : SimplicialObject.Augmented C)
    (hA : A.IsHypercovering J) :
    ((toOverFamily.{w} A).obj (op <| SimplexCategory.mk 0)).toSieve ∈ J A.right := sorry

/-- Every matching map of the singleton-family lift is covering whenever the augmented object
satisfies its relative hypercovering condition. -/
theorem toOverFamily_matching_isCovering (A : SimplicialObject.Augmented C)
    (hA : A.IsHypercovering J) (n : ℕ) :
    SemiRepresentableFamily.OverFamily.covering J
      (SimplicialObject.matchingMap (toOverFamily.{w} A) n) := sorry

/-- Example 25.3.5 (Hypercovering by a simplicial object of the site): the singleton-family lift
is a hypercovering exactly when the augmentation and its relative matching maps are singleton
covering arrows. -/
@[stacks 0GM9]
theorem toOverFamily_isHypercovering_iff (A : SimplicialObject.Augmented C) :
    CategoryTheory.IsHypercovering J (toOverFamily.{w} A) ↔ A.IsHypercovering J := sorry

/-- Build the site-theoretic hypercovering associated to an augmented simplicial object satisfying
the relative covering conditions. -/
@[stacks 0GM9 "hypercovering from an augmented simplicial object"]
noncomputable def toHypercovering (A : SimplicialObject.Augmented C)
    (hA : A.IsHypercovering J) : Hypercovering.{w} J A.right :=
  Hypercovering.ofSimplicial (toOverFamily.{w} A)
    (toOverFamily_zero_isCovering A hA) (toOverFamily_matching_isCovering A hA)

/-- The hypercovering constructed from `A` has `A.toOverFamily` as its underlying simplicial
fixed-target family. -/
@[simp] theorem toHypercovering_toSimplicialObject (A : SimplicialObject.Augmented C)
    (hA : A.IsHypercovering J) :
    (toHypercovering.{w} A hA).toSimplicialObject = toOverFamily.{w} A := sorry

end CategoryTheory.SimplicialObject.Augmented
