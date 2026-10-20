module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Routes in the relative-inertia square

This module owns the target projection and the two canonical routes from
relative inertia to inertia of the target.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedNatIso BasedNatTrans
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

namespace RelativeInertia

namespace Square

/-- Project based relative inertia to the target category. -/
@[stacks 04Z6 "target projection in the relative-inertia square"]
def toTarget (F : X ⥤ᵇ Y) : relativeInertia F ⥤ᵇ Y :=
  RelativeInertia.forget F ⋙ F

/-- Route from relative inertia through the target and its neutral inertia section. -/
@[stacks 04Z6 "target route in the relative-inertia square"]
def viaTarget (F : X ⥤ᵇ Y) :
    relativeInertia F ⥤ᵇ inertia Y :=
  toTarget F ⋙ Inertia.identitySection Y

/-- Route from relative inertia through absolute inertia of the source. -/
@[stacks 04Z6 "source route in the relative-inertia square"]
def viaSource (F : X ⥤ᵇ Y) :
    relativeInertia F ⥤ᵇ inertia Y :=
  RelativeInertia.toInertia F ⋙ Inertia.map F

end Square

end RelativeInertia

end BasedCategory
end CategoryTheory
