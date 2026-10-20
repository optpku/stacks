/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Computations.Action.Objects
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Identity.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Composition.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison computations for the based-inertia pseudofunctor

This leaf identifies the packaged identity and composition comparisons with their canonical
based owners and exposes both directions at cell, component, and underlying-arrow levels.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

namespace Inertia

/-- The ordinary identity comparison is the explicit componentwise inertia isomorphism. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor identity comparison"]
theorem pseudofunctor.mapId (X : BasedCategory.{v₁, u₁} C) :
    (pseudofunctor C).mapId X = Inertia.mapIdIso X := sorry

/-- The forward identity-comparison component is the canonical objectwise comparison. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor identity forward component"]
theorem pseudofunctor.mapId.hom.app
    (X : BasedCategory.{v₁, u₁} C) (A : (inertia X).obj) :
    ((pseudofunctor C).mapId X).hom.toNatTrans.app A =
      (Inertia.mapIdIso.app X A).hom := sorry

/-- The inverse identity-comparison component is the canonical reverse objectwise
comparison. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor identity inverse component"]
theorem pseudofunctor.mapId.inv.app
    (X : BasedCategory.{v₁, u₁} C) (A : (inertia X).obj) :
    ((pseudofunctor C).mapId X).inv.toNatTrans.app A =
      (Inertia.mapIdIso.app X A).inv := sorry

/-- The ambient arrow underlying a forward identity-comparison component is an identity. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor identity forward underlying component"]
theorem pseudofunctor.mapId.hom.app.underlying
    (X : BasedCategory.{v₁, u₁} C) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom
        (((pseudofunctor C).mapId X).hom.toNatTrans.app A) =
      𝟙 A.obj := sorry

/-- Every forward packaged identity-comparison component is vertical over the identity on the
base. -/
theorem pseudofunctor.mapId.hom.app.isHomLift
    (X : BasedCategory.{v₁, u₁} C) (A : (inertia X).obj) :
    (inertia X).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      (((pseudofunctor C).mapId X).hom.toNatTrans.app A) := sorry

/-- The ambient arrow underlying an inverse identity-comparison component is an identity. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor identity inverse underlying component"]
theorem pseudofunctor.mapId.inv.app.underlying
    (X : BasedCategory.{v₁, u₁} C) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom
        (((pseudofunctor C).mapId X).inv.toNatTrans.app A) =
      𝟙 A.obj := sorry

/-- Every inverse packaged identity-comparison component is vertical over the identity on the
base. -/
theorem pseudofunctor.mapId.inv.app.isHomLift
    (X : BasedCategory.{v₁, u₁} C) (A : (inertia X).obj) :
    (inertia X).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      (((pseudofunctor C).mapId X).inv.toNatTrans.app A) := sorry

/-- The ordinary composition comparison is the explicit componentwise inertia isomorphism. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor composition comparison"]
theorem pseudofunctor.mapComp
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) :
    (pseudofunctor C).mapComp F G = Inertia.mapCompIso F G := sorry

/-- The forward composition-comparison component is the canonical objectwise comparison. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor composition forward component"]
theorem pseudofunctor.mapComp.hom.app
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) (A : (inertia X).obj) :
    ((pseudofunctor C).mapComp F G).hom.toNatTrans.app A =
      (Inertia.mapCompIso.app F G A).hom := sorry

/-- The inverse composition-comparison component is the canonical reverse objectwise
comparison. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor composition inverse component"]
theorem pseudofunctor.mapComp.inv.app
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) (A : (inertia X).obj) :
    ((pseudofunctor C).mapComp F G).inv.toNatTrans.app A =
      (Inertia.mapCompIso.app F G A).inv := sorry

/-- The ambient arrow underlying a forward composition-comparison component is an identity. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor composition forward underlying component"]
theorem pseudofunctor.mapComp.hom.app.underlying
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom
        (((pseudofunctor C).mapComp F G).hom.toNatTrans.app A) =
      𝟙 (((Inertia.map F ⋙ Inertia.map G).obj A).obj) := sorry

/-- Every forward packaged composition-comparison component is vertical over the identity on the
base. -/
theorem pseudofunctor.mapComp.hom.app.isHomLift
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) (A : (inertia X).obj) :
    (inertia Z).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      (((pseudofunctor C).mapComp F G).hom.toNatTrans.app A) := sorry

/-- The ambient arrow underlying an inverse composition-comparison component is an identity. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor composition inverse underlying component"]
theorem pseudofunctor.mapComp.inv.app.underlying
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) (A : (inertia X).obj) :
    CategoryTheory.RelativeInertia.hom
        (((pseudofunctor C).mapComp F G).inv.toNatTrans.app A) =
      𝟙 (((Inertia.map F ⋙ Inertia.map G).obj A).obj) := sorry

/-- Every inverse packaged composition-comparison component is vertical over the identity on the
base. -/
theorem pseudofunctor.mapComp.inv.app.isHomLift
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) (A : (inertia X).obj) :
    (inertia Z).p.IsHomLift
      (𝟙 ((inertia X).p.obj A))
      (((pseudofunctor C).mapComp F G).inv.toNatTrans.app A) := sorry

end Inertia

end BasedCategory
end CategoryTheory
