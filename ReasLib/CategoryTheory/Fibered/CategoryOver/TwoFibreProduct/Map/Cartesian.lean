/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Map.Construction
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cospan.Cartesian
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian presentation of two-fibre-product maps

This leaf compares the fixed-universe bicategorical map with the heterogeneous explicit
pseudo-pullback owner.  The neutral cospan conversion is owned by
`FiberedCategoryOver.CospanTransform.toCartesian`.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct

variable
  {X₁ Y₁ S₁ X₂ Y₂ S₂ :
    FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}
  {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
  {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

/-- The cartesian based functor underlying the fixed two-fibre-product map is the heterogeneous
explicit pseudo-pullback map of its cartesian cospan presentation. -/
@[simp, stacks 04Y1 "cartesian presentation of a two-fibre-product map"]
theorem map.toCartesianBasedFunctor (psi : CospanTransform F₁ G₁ F₂ G₂) :
    FiberedCategoryOver.toCartesianBasedFunctor (map psi) =
      BasedCategory.PseudoPullback.cartesianMap
        (FiberedCategoryOver.CospanTransform.toCartesian psi) := sorry

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
