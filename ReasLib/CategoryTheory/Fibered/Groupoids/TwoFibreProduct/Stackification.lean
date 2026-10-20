/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.TwoFibreProduct.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Criteria
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stackifications and two-fibre products of groupoid-fibred categories

The groupoid-fibred two-fibre-product map has its own owner.  This leaf records the stronger
stackification statement while leaving the local-equivalence closure in its narrower sibling.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace FiberedCategoryOver.Groupoids.TwoFibreProduct

variable
  {X₁ Y₁ S₁ X₂ Y₂ S₂ :
    FiberedCategoryOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} C}
  {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
  {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

namespace map

/-- A componentwise local equivalence induces a stackification of groupoid-fibred
two-fibre products when the two target ends are stacks and their common target is a prestack.
The prestack hypothesis is the exact descent condition needed for two-fibre-product closure. -/
@[stacks 04Y2 "groupoid two-fibre-product stackification from local equivalences"]
theorem isStackification_of_isLocalEquivalence
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (hleft : FiberedCategoryOver.Groupoids.Hom.IsLocalEquivalence J ψ.left)
    (hright : FiberedCategoryOver.Groupoids.Hom.IsLocalEquivalence J ψ.right)
    (hbase : FiberedCategoryOver.Groupoids.Hom.IsLocalEquivalence J ψ.base)
    [IsStack.OnSite J X₂.p] [IsStack.OnSite J Y₂.p]
    [IsPrestack.OnSite J S₂.p] :
    FiberedCategoryOver.Groupoids.Hom.IsStackification J
      (CategoryTheory.TwoFibreProduct.map ψ) := sorry

/-- A componentwise stackification cospan map of groupoid-fibred categories is a
stackification.  Its target stack condition is supplied by two-fibre-product closure. -/
@[stacks 04Y2 "two-fibre-products preserve stackifications"]
theorem isStackification
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (hleft : FiberedCategoryOver.Groupoids.Hom.IsStackification J ψ.left)
    (hright : FiberedCategoryOver.Groupoids.Hom.IsStackification J ψ.right)
    (hbase : FiberedCategoryOver.Groupoids.Hom.IsStackification J ψ.base) :
    FiberedCategoryOver.Groupoids.Hom.IsStackification J
      (CategoryTheory.TwoFibreProduct.map ψ) := sorry

/-- Given stackifications of the three groupoid-fibred objects in a cospan, compatible target
legs exist and their componentwise two-fibre-product map is a stackification. -/
@[stacks 04Y2 "source-faithful groupoid existence form"]
theorem exists_of_stackifications
    (iX : X₁ ⟶ X₂) (iY : Y₁ ⟶ Y₂) (iS : S₁ ⟶ S₂)
    (hX : FiberedCategoryOver.Groupoids.Hom.IsStackification J iX)
    (hY : FiberedCategoryOver.Groupoids.Hom.IsStackification J iY)
    (hS : FiberedCategoryOver.Groupoids.Hom.IsStackification J iS) :
    ∃ F₂ : X₂ ⟶ S₂, ∃ G₂ : Y₂ ⟶ S₂,
      ∃ ψ : CospanTransform F₁ G₁ F₂ G₂,
        ψ.left = iX ∧ ψ.right = iY ∧ ψ.base = iS ∧
          FiberedCategoryOver.Groupoids.Hom.IsStackification J
            (CategoryTheory.TwoFibreProduct.map ψ) := sorry

end map

end FiberedCategoryOver.Groupoids.TwoFibreProduct

end CategoryTheory
