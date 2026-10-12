/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Counit.Construction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia comparison counit computations

This module exposes component formulas for the explicit counit isomorphism of
the relative-inertia comparison inverse.
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

/-- The base component of the forward explicit comparison counit is the stored base
isomorphism. -/
@[simp, stacks 034H "diagonal-comparison counit component base projection"]
theorem RelativeInertia.diagonalComparison.counitIso.app.hom.base (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.baseMap (RelativeInertia.diagonalComparison.counitIso.app F P).hom =
      (RelativeInertia.diagonalComparison.counitIso.app.baseIso F P).hom := sorry

/-- The first component of the forward explicit comparison counit is the identity component. -/
@[simp, stacks 034H "diagonal-comparison counit component first projection"]
theorem RelativeInertia.diagonalComparison.counitIso.app.hom.fst (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.fstMap (RelativeInertia.diagonalComparison.counitIso.app F P).hom =
      (RelativeInertia.diagonalComparison.counitIso.app.fstIso F P).hom := sorry

/-- The second component of the forward explicit comparison counit is the structural second
component. -/
@[simp, stacks 034H "diagonal-comparison counit component second projection"]
theorem RelativeInertia.diagonalComparison.counitIso.app.hom.snd (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.sndMap (RelativeInertia.diagonalComparison.counitIso.app F P).hom =
      (RelativeInertia.diagonalComparison.counitIso.app.sndIso F P).hom := sorry

/-- The base component of the inverse explicit comparison counit is the inverse stored base
isomorphism. -/
@[simp, stacks 034H "diagonal-comparison inverse counit base projection"]
theorem RelativeInertia.diagonalComparison.counitIso.app.inv.base (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.baseMap (RelativeInertia.diagonalComparison.counitIso.app F P).inv =
      (RelativeInertia.diagonalComparison.counitIso.app.baseIso F P).inv := sorry

/-- The first component of the inverse explicit comparison counit is the inverse identity
component. -/
@[simp, stacks 034H "diagonal-comparison inverse counit first projection"]
theorem RelativeInertia.diagonalComparison.counitIso.app.inv.fst (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.fstMap (RelativeInertia.diagonalComparison.counitIso.app F P).inv =
      (RelativeInertia.diagonalComparison.counitIso.app.fstIso F P).inv := sorry

/-- The second component of the inverse explicit comparison counit is the inverse structural
second component. -/
@[simp, stacks 034H "diagonal-comparison inverse counit second projection"]
theorem RelativeInertia.diagonalComparison.counitIso.app.inv.snd (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.sndMap (RelativeInertia.diagonalComparison.counitIso.app F P).inv =
      (RelativeInertia.diagonalComparison.counitIso.app.sndIso F P).inv := sorry

/-- The forward component of the based comparison counit is the explicit pseudo-pullback
component. -/
@[simp, stacks 034H "diagonal-comparison packaged counit forward component"]
theorem RelativeInertia.diagonalComparison.counitIso.hom.app (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.counitIso F).hom.toNatTrans.app P =
      (RelativeInertia.diagonalComparison.counitIso.app F P).hom := sorry

/-- Every forward packaged comparison-counit component is vertical over the identity of its base. -/
theorem RelativeInertia.diagonalComparison.counitIso.hom.app.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p.IsHomLift
      (𝟙 ((PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p.obj P))
      ((RelativeInertia.diagonalComparison.counitIso F).hom.toNatTrans.app P) := sorry

/-- The inverse component of the based comparison counit is the inverse explicit
pseudo-pullback component. -/
@[simp, stacks 034H "diagonal-comparison packaged counit inverse component"]
theorem RelativeInertia.diagonalComparison.counitIso.inv.app (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.counitIso F).inv.toNatTrans.app P =
      (RelativeInertia.diagonalComparison.counitIso.app F P).inv := sorry

/-- Every inverse packaged comparison-counit component is vertical over the identity of its base. -/
theorem RelativeInertia.diagonalComparison.counitIso.inv.app.isHomLift (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p.IsHomLift
      (𝟙 ((PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).p.obj P))
      ((RelativeInertia.diagonalComparison.counitIso F).inv.toNatTrans.app P) := sorry

/-- The base projection of a forward packaged comparison-counit component is the stored base
isomorphism. -/
@[simp, stacks 034H "diagonal-comparison packaged counit forward base projection"]
theorem RelativeInertia.diagonalComparison.counitIso.hom.app.base (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.baseMap
        ((RelativeInertia.diagonalComparison.counitIso F).hom.toNatTrans.app P) =
      (RelativeInertia.diagonalComparison.counitIso.app.baseIso F P).hom := sorry

/-- The first projection of a forward packaged comparison-counit component is the identity
component. -/
@[simp, stacks 034H "diagonal-comparison packaged counit forward first projection"]
theorem RelativeInertia.diagonalComparison.counitIso.hom.app.fst (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.fstMap
        ((RelativeInertia.diagonalComparison.counitIso F).hom.toNatTrans.app P) =
      (RelativeInertia.diagonalComparison.counitIso.app.fstIso F P).hom := sorry

/-- The second projection of a forward packaged comparison-counit component is the structural
second component. -/
@[simp, stacks 034H "diagonal-comparison packaged counit forward second projection"]
theorem RelativeInertia.diagonalComparison.counitIso.hom.app.snd (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.sndMap
        ((RelativeInertia.diagonalComparison.counitIso F).hom.toNatTrans.app P) =
      (RelativeInertia.diagonalComparison.counitIso.app.sndIso F P).hom := sorry

/-- The base projection of an inverse packaged comparison-counit component is the inverse stored
base isomorphism. -/
@[simp, stacks 034H "diagonal-comparison packaged counit inverse base projection"]
theorem RelativeInertia.diagonalComparison.counitIso.inv.app.base (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.baseMap
        ((RelativeInertia.diagonalComparison.counitIso F).inv.toNatTrans.app P) =
      (RelativeInertia.diagonalComparison.counitIso.app.baseIso F P).inv := sorry

/-- The first projection of an inverse packaged comparison-counit component is the inverse
identity component. -/
@[simp, stacks 034H "diagonal-comparison packaged counit inverse first projection"]
theorem RelativeInertia.diagonalComparison.counitIso.inv.app.fst (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.fstMap
        ((RelativeInertia.diagonalComparison.counitIso F).inv.toNatTrans.app P) =
      (RelativeInertia.diagonalComparison.counitIso.app.fstIso F P).inv := sorry

/-- The second projection of an inverse packaged comparison-counit component is the inverse
structural second component. -/
@[simp, stacks 034H "diagonal-comparison packaged counit inverse second projection"]
theorem RelativeInertia.diagonalComparison.counitIso.inv.app.snd (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    PseudoPullback.sndMap
        ((RelativeInertia.diagonalComparison.counitIso F).inv.toNatTrans.app P) =
      (RelativeInertia.diagonalComparison.counitIso.app.sndIso F P).inv := sorry

end BasedFunctor

end CategoryTheory
