/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Naturality.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for relative-to-absolute inertia naturality

This leaf exposes the objectwise components and underlying-arrow readouts of the canonical
relative-to-absolute comparison.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂'

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]
variable
    {S₁ : BasedCategory.{v₁, u₁} C} {S₁' : BasedCategory.{v₁', u₁'} C}
    {S₂ : BasedCategory.{v₂, u₂} C} {S₂' : BasedCategory.{v₂', u₂'} C}
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}

namespace RelativeInertia.toInertia

namespace naturalityIso

/-- The forward objectwise comparison has identity underlying arrow. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia component forward underlying arrow"]
theorem component.hom.underlying
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    CategoryTheory.RelativeInertia.hom (naturalityIso.component G G' comm X).hom =
      𝟙 _ := sorry

/-- The inverse objectwise comparison has identity underlying arrow. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia component inverse underlying arrow"]
theorem component.inv.underlying
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    CategoryTheory.RelativeInertia.hom (naturalityIso.component G G' comm X).inv =
      𝟙 _ := sorry

/-- The forward component of the based naturality isomorphism is the canonical objectwise
identity-arrow comparison. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia naturality forward component"]
theorem hom.app
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    (naturalityIso G G' comm).hom.toNatTrans.app X =
      (naturalityIso.component G G' comm X).hom := sorry

/-- The inverse component of the based naturality isomorphism is the canonical reverse
identity-arrow comparison. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia naturality inverse component"]
theorem inv.app
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    (naturalityIso G G' comm).inv.toNatTrans.app X =
      (naturalityIso.component G G' comm X).inv := sorry

/-- The arrow underlying each forward naturality component is an identity. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia naturality forward underlying arrow"]
theorem hom.app.underlying
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    CategoryTheory.RelativeInertia.hom
        ((naturalityIso G G' comm).hom.toNatTrans.app X) =
      𝟙 (G.toFunctor.obj X.obj) := sorry

/-- The arrow underlying each inverse naturality component is an identity. -/
@[simp, stacks 04Z5 "relative-to-absolute inertia naturality inverse underlying arrow"]
theorem inv.app.underlying
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    CategoryTheory.RelativeInertia.hom
        ((naturalityIso G G' comm).inv.toNatTrans.app X) =
      𝟙 (G.toFunctor.obj X.obj) := sorry

end naturalityIso

end RelativeInertia.toInertia

end BasedCategory
end CategoryTheory
