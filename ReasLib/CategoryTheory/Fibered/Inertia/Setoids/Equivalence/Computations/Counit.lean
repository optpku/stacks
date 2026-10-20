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

/-- The forward component of the canonical counit is the identity. -/
@[simp] theorem counitIso.hom.app (F : X ⥤ᵇ Y) (x : X.obj) :
    (counitIso F).hom.toNatTrans.app x = 𝟙 x := sorry

/-- The inverse component of the canonical counit is the identity. -/
@[simp] theorem counitIso.inv.app (F : X ⥤ᵇ Y) (x : X.obj) :
    (counitIso F).inv.toNatTrans.app x = 𝟙 x := sorry

end BasedCategory.RelativeInertia.forget
end CategoryTheory
