/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber.Cartesian
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Cospan
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Forget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian cospan transformations of fibred categories

This leaf forgets a fixed-universe cospan transformation in `FiberedCategoryOver C` to the
heterogeneous `CartesianCospanTransform` owner.  The construction belongs to the cospan API;
two-fibre-product consumers only use it through their induced map comparison.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.CospanTransform

variable
  {X₁ Y₁ S₁ X₂ Y₂ S₂ :
    FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}
  {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
  {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

namespace toCartesian

/-- The left component of the forgotten fixed cospan transformation preserves strongly
cartesian arrows. -/
@[stacks 04Y1 "left cartesian preservation for cospan presentation"]
theorem leftPreserves (psi : Bicategory.CospanTransform F₁ G₁ F₂ G₂) :
    (LocallyInduced.TwoFibreProduct.CospanTransform.forget psi).left.PreservesStronglyCartesian := sorry

/-- The right component of the forgotten fixed cospan transformation preserves strongly
cartesian arrows. -/
@[stacks 04Y1 "right cartesian preservation for cospan presentation"]
theorem rightPreserves (psi : Bicategory.CospanTransform F₁ G₁ F₂ G₂) :
    (LocallyInduced.TwoFibreProduct.CospanTransform.forget psi).right.PreservesStronglyCartesian := sorry

/-- The common-target component of the forgotten fixed cospan transformation preserves
strongly cartesian arrows. -/
@[stacks 04Y1 "base cartesian preservation for cospan presentation"]
theorem basePreserves (psi : Bicategory.CospanTransform F₁ G₁ F₂ G₂) :
    (LocallyInduced.TwoFibreProduct.CospanTransform.forget psi).base.PreservesStronglyCartesian := sorry

end toCartesian

/-- Regard a fixed-universe cospan transformation of fibred categories as a heterogeneous
cartesian cospan transformation. Its based data are the canonical locally induced forgetful
presentation. -/
@[stacks 04Y1 "cartesian presentation of a cospan transformation"]
noncomputable def toCartesian (psi : Bicategory.CospanTransform F₁ G₁ F₂ G₂) :
    CartesianCospanTransform
      (FiberedCategoryOver.toCartesianBasedFunctor F₁)
      (FiberedCategoryOver.toCartesianBasedFunctor G₁)
      (FiberedCategoryOver.toCartesianBasedFunctor F₂)
      (FiberedCategoryOver.toCartesianBasedFunctor G₂) :=
  CartesianCospanTransform.ofBased
    (LocallyInduced.TwoFibreProduct.CospanTransform.forget psi)
    (toCartesian.leftPreserves psi)
    (toCartesian.rightPreserves psi)
    (toCartesian.basePreserves psi)

/-- Forgetting the cartesian presentation recovers the canonical based cospan
transformation. -/
@[simp, stacks 04Y1 "based readout of cartesian cospan presentation"]
theorem toCartesian.toBased (psi : Bicategory.CospanTransform F₁ G₁ F₂ G₂) :
    (toCartesian psi).toBased =
      LocallyInduced.TwoFibreProduct.CospanTransform.forget psi := sorry

/-- The left component of the cartesian presentation is the canonical cartesian functor
underlying the fixed left component. -/
@[simp, stacks 04Y1 "left readout of cartesian cospan presentation"]
theorem toCartesian.left (psi : Bicategory.CospanTransform F₁ G₁ F₂ G₂) :
    (toCartesian psi).left =
      FiberedCategoryOver.toCartesianBasedFunctor psi.left := sorry

/-- The right component of the cartesian presentation is the canonical cartesian functor
underlying the fixed right component. -/
@[simp, stacks 04Y1 "right readout of cartesian cospan presentation"]
theorem toCartesian.right (psi : Bicategory.CospanTransform F₁ G₁ F₂ G₂) :
    (toCartesian psi).right =
      FiberedCategoryOver.toCartesianBasedFunctor psi.right := sorry

/-- The common-target component of the cartesian presentation is the canonical cartesian
functor underlying the fixed common-target component. -/
@[simp, stacks 04Y1 "base readout of cartesian cospan presentation"]
theorem toCartesian.base (psi : Bicategory.CospanTransform F₁ G₁ F₂ G₂) :
    (toCartesian psi).base =
      FiberedCategoryOver.toCartesianBasedFunctor psi.base := sorry

end FiberedCategoryOver.CospanTransform

end CategoryTheory

/- Axiom audit: the non-Prop cospan data are inherited from the canonical forgetful
transformation.  The proof debt introduced in this leaf is confined to the three preservation
witnesses and their readout equalities. -/
