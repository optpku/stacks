module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Unit.Construction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia comparison unit computations

This module exposes the explicit and packaged component formulas for the unit
of the diagonal-comparison inverse.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace BasedFunctor

variable {X Y : BasedCategory C}

/-- The underlying arrow of the forward comparison-unit component is the identity. -/
@[simp, stacks 034H "diagonal-comparison unit forward underlying arrow"]
theorem RelativeInertia.diagonalComparison.unitIso.app.hom.underlying (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    CategoryTheory.RelativeInertia.hom
        (RelativeInertia.diagonalComparison.unitIso.app F A).hom =
      𝟙 A.obj := sorry

/-- The underlying arrow of the inverse comparison-unit component is the identity. -/
@[simp, stacks 034H "diagonal-comparison unit inverse underlying arrow"]
theorem RelativeInertia.diagonalComparison.unitIso.app.inv.underlying (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    CategoryTheory.RelativeInertia.hom
        (RelativeInertia.diagonalComparison.unitIso.app F A).inv =
      𝟙 A.obj := sorry

/-- The forward component of the based comparison unit is the explicit identity-arrow
component. -/
@[simp, stacks 034H "diagonal-comparison packaged unit forward component"]
theorem RelativeInertia.diagonalComparison.unitIso.hom.app (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    (RelativeInertia.diagonalComparison.unitIso F).hom.toNatTrans.app A =
      (RelativeInertia.diagonalComparison.unitIso.app F A).hom := sorry

/-- The underlying arrow of every forward packaged comparison-unit component is an identity. -/
@[simp, stacks 034H "diagonal-comparison packaged unit forward underlying arrow"]
theorem RelativeInertia.diagonalComparison.unitIso.hom.app.underlying (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    CategoryTheory.RelativeInertia.hom
        ((RelativeInertia.diagonalComparison.unitIso F).hom.toNatTrans.app A) =
      𝟙 A.obj := sorry

/-- Every forward packaged comparison-unit component is vertical over the identity of its base. -/
theorem RelativeInertia.diagonalComparison.unitIso.hom.app.isHomLift (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    (CategoryTheory.RelativeInertia.projection F.toFunctor X.p).IsHomLift
      (𝟙 ((CategoryTheory.RelativeInertia.projection F.toFunctor X.p).obj A))
      ((RelativeInertia.diagonalComparison.unitIso F).hom.toNatTrans.app A) := sorry

/-- The inverse component of the based comparison unit is the inverse explicit identity-arrow
component. -/
@[simp, stacks 034H "diagonal-comparison packaged unit inverse component"]
theorem RelativeInertia.diagonalComparison.unitIso.inv.app (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    (RelativeInertia.diagonalComparison.unitIso F).inv.toNatTrans.app A =
      (RelativeInertia.diagonalComparison.unitIso.app F A).inv := sorry

/-- The underlying arrow of every inverse packaged comparison-unit component is an identity. -/
@[simp, stacks 034H "diagonal-comparison packaged unit inverse underlying arrow"]
theorem RelativeInertia.diagonalComparison.unitIso.inv.app.underlying (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    CategoryTheory.RelativeInertia.hom
        ((RelativeInertia.diagonalComparison.unitIso F).inv.toNatTrans.app A) =
      𝟙 A.obj := sorry

/-- Every inverse packaged comparison-unit component is vertical over the identity of its base. -/
theorem RelativeInertia.diagonalComparison.unitIso.inv.app.isHomLift (F : X ⥤ᵇ Y)
    (A : CategoryTheory.RelativeInertia F.toFunctor) :
    (CategoryTheory.RelativeInertia.projection F.toFunctor X.p).IsHomLift
      (𝟙 ((CategoryTheory.RelativeInertia.projection F.toFunctor X.p).obj A))
      ((RelativeInertia.diagonalComparison.unitIso F).inv.toNatTrans.app A) := sorry

end BasedFunctor

end CategoryTheory
