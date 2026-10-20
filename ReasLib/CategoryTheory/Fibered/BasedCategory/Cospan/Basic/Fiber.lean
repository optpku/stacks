module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Basic.Core
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.CatCospanTransform

/-!
# Fibers of based cospan transformations

This file forgets a universe-polymorphic based cospan transformation to the standard mathlib
`CatCospanTransform` on each fiber.
-/

@[expose] public section

namespace CategoryTheory

open BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

variable {C : Type u} [Category.{v} C]
variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}

namespace BasedCospanTransform

variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

/-- The ordinary left comparison obtained by restricting a based cospan transformation to the
standard fiber over `U`. -/
def fiber.leftIso (psi : BasedCospanTransform F₁ G₁ F₂ G₂) (U : C) :
    F₁.fiberFunctor U ⋙ psi.base.fiberFunctor U ≅
      psi.left.fiberFunctor U ⋙ F₂.fiberFunctor U :=
  (eqToIso (BasedFunctor.fiberFunctor.comp F₁ psi.base U)).symm ≪≫
    (BasedNatIso.fiber psi.leftIso U).symm ≪≫
      eqToIso (BasedFunctor.fiberFunctor.comp psi.left F₂ U)

/-- The ordinary right comparison obtained by restricting a based cospan transformation to the
standard fiber over `U`. -/
def fiber.rightIso (psi : BasedCospanTransform F₁ G₁ F₂ G₂) (U : C) :
    G₁.fiberFunctor U ⋙ psi.base.fiberFunctor U ≅
      psi.right.fiberFunctor U ⋙ G₂.fiberFunctor U :=
  (eqToIso (BasedFunctor.fiberFunctor.comp G₁ psi.base U)).symm ≪≫
    (BasedNatIso.fiber psi.rightIso U).symm ≪≫
      eqToIso (BasedFunctor.fiberFunctor.comp psi.right G₂ U)

/-- Restrict a based cospan transformation to a universe-polymorphic ordinary categorical
cospan transformation on the standard fiber over `U`. -/
def fiber (psi : BasedCospanTransform F₁ G₁ F₂ G₂) (U : C) :
    Limits.CatCospanTransform
      (F₁.fiberFunctor U) (G₁.fiberFunctor U)
      (F₂.fiberFunctor U) (G₂.fiberFunctor U) where
  left := psi.left.fiberFunctor U
  right := psi.right.fiberFunctor U
  base := psi.base.fiberFunctor U
  squareLeft := ⟨fiber.leftIso psi U⟩
  squareRight := ⟨fiber.rightIso psi U⟩

/-- Restricting a based cospan transformation to a fiber retains its left component as the
induced left fiber functor. -/
@[simp]
theorem fiber.left (psi : BasedCospanTransform F₁ G₁ F₂ G₂) (U : C) :
    (fiber psi U).left = psi.left.fiberFunctor U := sorry

/-- Restricting a based cospan transformation to a fiber retains its right component as the
induced right fiber functor. -/
@[simp]
theorem fiber.right (psi : BasedCospanTransform F₁ G₁ F₂ G₂) (U : C) :
    (fiber psi U).right = psi.right.fiberFunctor U := sorry

/-- Restricting a based cospan transformation to a fiber retains its common-target component as
the induced base fiber functor. -/
@[simp]
theorem fiber.base (psi : BasedCospanTransform F₁ G₁ F₂ G₂) (U : C) :
    (fiber psi U).base = psi.base.fiberFunctor U := sorry

end BasedCospanTransform

end CategoryTheory
