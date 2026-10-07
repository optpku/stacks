module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Equivalence.Construction

@[expose] public section

universe u v vS w uY vY

namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace BasedCategory.RelativeInertia.forget

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vS, max w vS} C} {Y : BasedCategory.{vY, uY} C}

/-- The forward arrow of the relative-inertia unit component is the identity. -/
@[simp] theorem unitIsoApp.hom (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p)
    (A : (BasedCategory.relativeInertia F).obj) :
    CategoryTheory.RelativeInertia.hom (unitIsoApp F hX A).hom = 𝟙 A.obj := sorry

/-- The inverse arrow of the relative-inertia unit component is the identity. -/
@[simp] theorem unitIsoApp.inv (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p)
    (A : (BasedCategory.relativeInertia F).obj) :
    CategoryTheory.RelativeInertia.hom (unitIsoApp F hX A).inv = 𝟙 A.obj := sorry

/-- The forward component of the canonical unit is the explicit unit component. -/
@[simp] theorem unitIso.hom.app (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p)
    (A : (BasedCategory.relativeInertia F).obj) :
    (unitIso F hX).hom.toNatTrans.app A = (unitIsoApp F hX A).hom := sorry

/-- The inverse component of the canonical unit is the inverse explicit unit component. -/
@[simp] theorem unitIso.inv.app (F : X ⥤ᵇ Y) (hX : Functor.IsFibered.InSetoids X.p)
    (A : (BasedCategory.relativeInertia F).obj) :
    (unitIso F hX).inv.toNatTrans.app A = (unitIsoApp F hX A).inv := sorry

end BasedCategory.RelativeInertia.forget
end CategoryTheory
