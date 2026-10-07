module

public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Routes.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object computations for routes in the relative-inertia square

This leaf records the underlying functors and object actions of the three canonical
routes. Morphism formulas are kept in `Routes.MorphismComputations`.
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

/-- The target projection is the composite of relative-inertia forgetting with `F`. -/
@[simp, stacks 04Z6 "relative-inertia square target total-functor computation"]
theorem toTarget.toFunctor (F : X ⥤ᵇ Y) :
    (toTarget F).toFunctor =
      (RelativeInertia.forget F).toFunctor ⋙ F.toFunctor := sorry
/- Proof strategy: unfold `toTarget`. -/

/-- The target projection sends a relative-inertia object to the image of its underlying
source object. -/
@[simp, stacks 04Z6 "relative-inertia square target object computation"]
theorem toTarget.obj
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    (toTarget F).toFunctor.obj Z = F.toFunctor.obj Z.obj := sorry

/-- The target route is the expected composite on underlying functors. -/
@[simp, stacks 04Z6 "relative-inertia square target-route total-functor computation"]
theorem viaTarget.toFunctor (F : X ⥤ᵇ Y) :
    (viaTarget F).toFunctor =
      (toTarget F).toFunctor ⋙ (Inertia.identitySection Y).toFunctor := sorry
/- Proof strategy: unfold `viaTarget`. -/

/-- The target route retains the image of the underlying source object. -/
@[simp, stacks 04Z6 "relative-inertia square target-route object computation"]
theorem viaTarget.obj
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    ((viaTarget F).toFunctor.obj Z).obj = F.toFunctor.obj Z.obj := sorry

/-- The target route equips every image object with the identity automorphism. -/
@[simp, stacks 04Z6 "relative-inertia square target-route automorphism computation"]
theorem viaTarget.aut
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    ((viaTarget F).toFunctor.obj Z).aut = 1 := sorry

/-- The source route is the expected composite on underlying functors. -/
@[simp, stacks 04Z6 "relative-inertia square source-route total-functor computation"]
theorem viaSource.toFunctor (F : X ⥤ᵇ Y) :
    (viaSource F).toFunctor =
      (RelativeInertia.toInertia F).toFunctor ⋙ (Inertia.map F).toFunctor := sorry
/- Proof strategy: unfold `viaSource`. -/

/-- The source route applies `F` to the underlying source object. -/
@[simp, stacks 04Z6 "relative-inertia square source-route object computation"]
theorem viaSource.obj
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    ((viaSource F).toFunctor.obj Z).obj = F.toFunctor.obj Z.obj := sorry

/-- The source route transports the selected relative automorphism through `F`. -/
@[simp, stacks 04Z6 "relative-inertia square source-route automorphism computation"]
theorem viaSource.aut
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    ((viaSource F).toFunctor.obj Z).aut = F.toFunctor.mapIso Z.aut := sorry

end Square
end RelativeInertia
end BasedCategory
end CategoryTheory
