/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Identity.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison computations for based inertia

This leaf exposes the underlying-arrow and component projections of the
canonical identity comparison.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

namespace Inertia
namespace mapIdIso

/-- The underlying forward arrow of the based-inertia identity comparison is the identity. -/
@[simp, stacks 04Z4 "based inertia identity-comparison forward underlying arrow"]
theorem app.hom.underlying
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    CategoryTheory.RelativeInertia.hom (app S A).hom =
      𝟙 A.obj := sorry

/-- The underlying inverse arrow of the based-inertia identity comparison is the identity. -/
@[simp, stacks 04Z4 "based inertia identity-comparison inverse underlying arrow"]
theorem app.inv.underlying
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    CategoryTheory.RelativeInertia.hom (app S A).inv =
      𝟙 A.obj := sorry

/-- The packaged forward identity comparison is vertical over the identity on the base. -/
theorem hom.app.isHomLift
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    (inertia S).p.IsHomLift
      (𝟙 ((inertia S).p.obj A))
      ((Inertia.mapIdIso S).hom.toNatTrans.app A) := sorry

/-- The packaged inverse identity comparison is vertical over the identity on the base. -/
theorem inv.app.isHomLift
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    (inertia S).p.IsHomLift
      (𝟙 ((inertia S).p.obj A))
      ((Inertia.mapIdIso S).inv.toNatTrans.app A) := sorry

/-- The forward component of the based-inertia identity comparison is its explicit objectwise
comparison. -/
@[simp, stacks 04Z4 "based inertia identity-comparison forward component"]
theorem hom.app
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    (Inertia.mapIdIso S).hom.toNatTrans.app A =
      (app S A).hom := sorry

/-- The inverse component of the based-inertia identity comparison is the inverse explicit
objectwise comparison. -/
@[simp, stacks 04Z4 "based inertia identity-comparison inverse component"]
theorem inv.app
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    (Inertia.mapIdIso S).inv.toNatTrans.app A =
      (app S A).inv := sorry

end mapIdIso

end Inertia
end BasedCategory
end CategoryTheory
