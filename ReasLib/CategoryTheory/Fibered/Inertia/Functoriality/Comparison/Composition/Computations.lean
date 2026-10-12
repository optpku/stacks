/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Composition.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparison computations for based inertia

This leaf exposes the underlying-arrow and component projections of the
canonical composition comparison.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v u₁ v₁ v₂ u₂ v₃ u₃

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]
variable
    {S₁ : BasedCategory.{v₁, u₁} C} {S₂ : BasedCategory.{v₂, u₂} C}

namespace Inertia
namespace mapCompIso

/-- The underlying forward arrow of the based-inertia composition comparison is the identity. -/
@[simp, stacks 04Z4 "based inertia composition-comparison forward underlying arrow"]
theorem app.hom.underlying
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    CategoryTheory.RelativeInertia.hom (app G H A).hom =
      𝟙 (((Inertia.map G ⋙ Inertia.map H).obj A).obj) := sorry

/-- The underlying inverse arrow of the based-inertia composition comparison is the identity. -/
@[simp, stacks 04Z4 "based inertia composition-comparison inverse underlying arrow"]
theorem app.inv.underlying
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    CategoryTheory.RelativeInertia.hom (app G H A).inv =
      𝟙 (((Inertia.map G ⋙ Inertia.map H).obj A).obj) := sorry

/-- The packaged forward composition comparison is vertical over the identity on the base. -/
theorem hom.app.isHomLift
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    (inertia S₃).p.IsHomLift
      (𝟙 ((inertia S₁).p.obj A))
      ((Inertia.mapCompIso G H).hom.toNatTrans.app A) := sorry

/-- The packaged inverse composition comparison is vertical over the identity on the base. -/
theorem inv.app.isHomLift
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    (inertia S₃).p.IsHomLift
      (𝟙 ((inertia S₁).p.obj A))
      ((Inertia.mapCompIso G H).inv.toNatTrans.app A) := sorry

/-- The forward component of the based-inertia composition comparison is its explicit objectwise
comparison. -/
@[simp, stacks 04Z4 "based inertia composition-comparison forward component"]
theorem hom.app
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    (Inertia.mapCompIso G H).hom.toNatTrans.app A =
      (app G H A).hom := sorry

/-- The inverse component of the based-inertia composition comparison is the inverse explicit
objectwise comparison. -/
@[simp, stacks 04Z4 "based inertia composition-comparison inverse component"]
theorem inv.app
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    (Inertia.mapCompIso G H).inv.toNatTrans.app A =
      (app G H A).inv := sorry

end mapCompIso

end Inertia
end BasedCategory
end CategoryTheory
