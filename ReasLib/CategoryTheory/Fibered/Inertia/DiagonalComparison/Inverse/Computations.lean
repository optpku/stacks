/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Inverse.Construction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative inertia comparison inverse computations

This module exposes the structural-component and object/map computations for the
explicit inverse to the relative-inertia comparison.
-/

open CategoryTheory
open CategoryTheory.Limits
open BasedCategory
open BasedFunctor
open scoped Bicategory

universe uC vC uS vS uS' vS'

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

namespace BasedFunctor

variable {X Y : BasedCategory C}

/-- The forward arrow of the first structural component is the first projection of the inner
structural isomorphism. -/
@[simp, stacks 034H "diagonal-comparison inverse first-component forward arrow"]
theorem RelativeInertia.diagonalComparison.inverse.fstIso.hom (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.inverse.fstIso F P).hom =
      PseudoPullback.fstMap
        (RelativeInertia.diagonalComparison.inverse.innerIso F P).hom := sorry

/-- The inverse arrow of the first structural component is the first projection of the inverse
inner structural isomorphism. -/
@[simp, stacks 034H "diagonal-comparison inverse first-component inverse arrow"]
theorem RelativeInertia.diagonalComparison.inverse.fstIso.inv (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.inverse.fstIso F P).inv =
      PseudoPullback.fstMap
        (RelativeInertia.diagonalComparison.inverse.innerIso F P).inv := sorry

/-- The forward arrow of the second structural component is the second projection of the inner
structural isomorphism. -/
@[simp, stacks 034H "diagonal-comparison inverse second-component forward arrow"]
theorem RelativeInertia.diagonalComparison.inverse.sndIso.hom (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.inverse.sndIso F P).hom =
      PseudoPullback.sndMap
        (RelativeInertia.diagonalComparison.inverse.innerIso F P).hom := sorry

/-- The inverse arrow of the second structural component is the second projection of the inverse
inner structural isomorphism. -/
@[simp, stacks 034H "diagonal-comparison inverse second-component inverse arrow"]
theorem RelativeInertia.diagonalComparison.inverse.sndIso.inv (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.inverse.sndIso F P).inv =
      PseudoPullback.sndMap
        (RelativeInertia.diagonalComparison.inverse.innerIso F P).inv := sorry

/-- The forward arrow of the recovered relative-inertia automorphism is the first structural
component followed by the inverse second component. -/
@[simp, stacks 034H "diagonal-comparison recovered automorphism forward arrow"]
theorem RelativeInertia.diagonalComparison.inverse.aut.hom (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.inverse.aut F P).hom =
      (RelativeInertia.diagonalComparison.inverse.fstIso F P).hom ≫
        (RelativeInertia.diagonalComparison.inverse.sndIso F P).inv := sorry

/-- The inverse arrow of the recovered relative-inertia automorphism is the second structural
component followed by the inverse first component. -/
@[simp, stacks 034H "diagonal-comparison recovered automorphism inverse arrow"]
theorem RelativeInertia.diagonalComparison.inverse.aut.inv (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (RelativeInertia.diagonalComparison.inverse.aut F P).inv =
      (RelativeInertia.diagonalComparison.inverse.sndIso F P).hom ≫
        (RelativeInertia.diagonalComparison.inverse.fstIso F P).inv := sorry

/-- The recovered relative-inertia object lies over the common base object of the self-pullback
object. -/
@[simp, stacks 034H "diagonal-comparison inverse base-object computation"]
theorem RelativeInertia.diagonalComparison.inverse.obj.base (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    (CategoryTheory.RelativeInertia.projection F.toFunctor X.p).obj
        ((RelativeInertia.diagonalComparison.inverse F).obj P) =
      PseudoPullback.baseObj P := sorry

/-- The object underlying the recovered relative-inertia object is the first projection of the
self-pullback object. -/
@[simp, stacks 034H "diagonal-comparison inverse underlying-object computation"]
theorem RelativeInertia.diagonalComparison.inverse.obj.underlying (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    ((RelativeInertia.diagonalComparison.inverse F).obj P).obj =
      PseudoPullback.fstObj P := sorry

/-- The automorphism of the recovered relative-inertia object is the quotient of the two
structural component isomorphisms. -/
@[simp, stacks 034H "diagonal-comparison inverse object automorphism computation"]
theorem RelativeInertia.diagonalComparison.inverse.obj.aut (F : X ⥤ᵇ Y)
    (P : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj) :
    ((RelativeInertia.diagonalComparison.inverse F).obj P).aut =
      RelativeInertia.diagonalComparison.inverse.aut F P := sorry

/-- The recovered relative-inertia morphism lies over the common base map of the self-pullback
morphism, transported through the canonical first-component base isomorphisms. -/
@[simp, stacks 034H "diagonal-comparison inverse base-map computation"]
theorem RelativeInertia.diagonalComparison.inverse.map.base (F : X ⥤ᵇ Y)
    {P Q : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj}
    (φ : P ⟶ Q) :
    (CategoryTheory.RelativeInertia.projection F.toFunctor X.p).map
        ((RelativeInertia.diagonalComparison.inverse F).map φ) =
      (PseudoPullback.fstBaseIso P).hom ≫ PseudoPullback.baseMap φ ≫
        (PseudoPullback.fstBaseIso Q).inv := sorry

/-- The underlying arrow of the recovered relative-inertia morphism is the first projection of
the self-pullback morphism. -/
@[simp, stacks 034H "diagonal-comparison inverse underlying-map computation"]
theorem RelativeInertia.diagonalComparison.inverse.map.hom (F : X ⥤ᵇ Y)
    {P Q : (PseudoPullback (relativeDiagonal F) (relativeDiagonal F)).obj}
    (φ : P ⟶ Q) :
    CategoryTheory.RelativeInertia.hom
        ((RelativeInertia.diagonalComparison.inverse F).map φ) =
      PseudoPullback.fstMap φ := sorry

end BasedFunctor

end CategoryTheory
