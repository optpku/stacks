/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Computations.Action

/-!
# Identity comparison computations for fibred relative inertia
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

/-- The identity comparison of fibred relative inertia is the canonical lift
of its based identity comparison. -/
@[simp]
theorem pseudofunctor.mapId
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    (pseudofunctor C).mapId S =
      FiberedCategoryOver.BasedFunctorIso.lift
        ((basedPseudofunctor C).mapId S) := by
  rfl

/-- The forward fibred relative-inertia identity comparison forgets to the
underlying based comparison cell. -/
@[simp]
theorem pseudofunctor.mapId.hom.toBasedNatTrans
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    FiberedCategoryOver.toBasedNatTrans
        ((pseudofunctor C).mapId S).hom =
      ((basedPseudofunctor C).mapId S).hom := by
  rfl

/-- The inverse fibred relative-inertia identity comparison forgets to the
underlying based comparison cell. -/
@[simp]
theorem pseudofunctor.mapId.inv.toBasedNatTrans
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    FiberedCategoryOver.toBasedNatTrans
        ((pseudofunctor C).mapId S).inv =
      ((basedPseudofunctor C).mapId S).inv := by
  rfl

/-- The forward identity comparison component is the corresponding component
of the based relative-inertia pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapId.hom.app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapId S).hom).app A =
      ((basedPseudofunctor C).mapId S).hom.toNatTrans.app A := by
  rfl

/-- The inverse identity comparison component is the corresponding component
of the based relative-inertia pseudofunctor. -/
@[simp]
theorem pseudofunctor.mapId.inv.app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    (FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapId S).inv).app A =
      ((basedPseudofunctor C).mapId S).inv.toNatTrans.app A := by
  rfl

/-- Every forward component of the packaged fibred relative-inertia identity comparison is
vertical over the identity base arrow. -/
theorem pseudofunctor.mapId.hom.app.isHomLift
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    (FiberedCategoryOver.relativeInertia S.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia S.hom).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapId S).hom).app A) := by
  exact (FiberedCategoryOver.toBasedNatTrans
    ((pseudofunctor C).mapId S).hom).isHomLift rfl

/-- Every inverse component of the packaged fibred relative-inertia identity comparison is
vertical over the identity base arrow. -/
theorem pseudofunctor.mapId.inv.app.isHomLift
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    (FiberedCategoryOver.relativeInertia S.hom).p.IsHomLift
      (𝟙 ((FiberedCategoryOver.relativeInertia S.hom).p.obj A))
      ((FiberedCategoryOver.toNatTrans
        ((pseudofunctor C).mapId S).inv).app A) := by
  exact (FiberedCategoryOver.toBasedNatTrans
    ((pseudofunctor C).mapId S).inv).isHomLift rfl

/-- The ambient arrow underlying a forward identity-comparison component is
the identity of the underlying relative-inertia object. -/
@[simp]
theorem pseudofunctor.mapId.hom.app.underlying
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapId S).hom).app A) =
      𝟙 A.obj := by
  change (((𝟙 A.obj ≫ 𝟙 A.obj) ≫ 𝟙 A.obj) ≫ (𝟙 A.obj ≫ 𝟙 A.obj)) ≫
    𝟙 A.obj = 𝟙 A.obj
  simp only [Category.id_comp]

/-- The ambient arrow underlying an inverse identity-comparison component is
the identity of the underlying relative-inertia object. -/
@[simp]
theorem pseudofunctor.mapId.inv.app.underlying
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C)))
    (A : ((pseudofunctor C).obj S).total) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toNatTrans
          ((pseudofunctor C).mapId S).inv).app A) =
      𝟙 A.obj := by
  change 𝟙 A.obj ≫ ((𝟙 A.obj ≫ 𝟙 A.obj) ≫ (𝟙 A.obj ≫ (𝟙 A.obj ≫ 𝟙 A.obj))) =
    𝟙 A.obj
  simp only [Category.id_comp]

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
