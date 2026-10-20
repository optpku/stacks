/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.IdentitySection.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the identity-section strong transformation

This leaf owns component, underlying-arrow, and packaged strong-transformation readouts.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.BasedCategory.Inertia

open BasedCategory BasedFunctor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace identitySection.naturalityIso

/-- The forward identity-section naturality component is the explicit identity-arrow
comparison. -/
@[simp, stacks 04Z3 "based-inertia identity-section forward component computation"]
theorem hom.app
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    (identitySection.naturalityIso F).hom.toNatTrans.app x =
      (component F x).hom := sorry

/-- The inverse identity-section naturality component is the reverse explicit comparison. -/
@[simp, stacks 04Z3 "based-inertia identity-section inverse component computation"]
theorem inv.app
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    (identitySection.naturalityIso F).inv.toNatTrans.app x =
      (component F x).inv := sorry

/-- The forward explicit identity-section comparison has the identity underlying arrow. -/
@[simp, stacks 04Z3 "based-inertia identity-section forward underlying arrow"]
theorem component.hom.underlying
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    CategoryTheory.RelativeInertia.hom (component F x).hom =
      𝟙 (F.toFunctor.obj x) := sorry

/-- The inverse explicit identity-section comparison has the identity underlying arrow. -/
@[simp, stacks 04Z3 "based-inertia identity-section inverse underlying arrow"]
theorem component.inv.underlying
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    CategoryTheory.RelativeInertia.hom (component F x).inv =
      𝟙 (F.toFunctor.obj x) := sorry

/-- The forward identity-section naturality component has the identity underlying arrow. -/
@[simp, stacks 04Z3 "based-inertia identity-section packaged forward underlying arrow"]
theorem hom.app.underlying
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    CategoryTheory.RelativeInertia.hom
        ((identitySection.naturalityIso F).hom.toNatTrans.app x) =
      𝟙 (F.toFunctor.obj x) := sorry

/-- The inverse identity-section naturality component has the identity underlying arrow. -/
@[simp, stacks 04Z3 "based-inertia identity-section packaged inverse underlying arrow"]
theorem inv.app.underlying
    {X Y : BasedCategory.{vS, max w vS} C} (F : X ⥤ᵇ Y) (x : X.obj) :
    CategoryTheory.RelativeInertia.hom
        ((identitySection.naturalityIso F).inv.toNatTrans.app x) =
      𝟙 (F.toFunctor.obj x) := sorry

end identitySection.naturalityIso

namespace identitySection.strongTrans

/-- The component of the based-inertia identity-section transformation is the identity
section. -/
@[simp, stacks 04Z3 "based-inertia identity-section strong transformation component"]
theorem app (X : BasedCategory.{vS, max w vS} C) :
    (identitySection.strongTrans C).app X = identitySection X := sorry

/-- The naturality isomorphism of the based-inertia identity section is the explicit
identity-arrow comparison. -/
@[simp, stacks 04Z3 "based-inertia identity-section strong transformation naturality"]
theorem naturality {X Y : BasedCategory.{vS, max w vS} C} (F : X ⟶ Y) :
    (identitySection.strongTrans C).naturality F =
      identitySection.naturalityIso F := sorry

end identitySection.strongTrans

end CategoryTheory.BasedCategory.Inertia
