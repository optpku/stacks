/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Square.Routes.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison computations in the relative-inertia square

This module exposes the explicit and packaged component formulas for the
canonical comparison between the two routes.
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

/-- The underlying forward arrow of the objectwise comparison is the identity. -/
@[simp, stacks 04Z6 "relative-inertia square forward component underlying arrow"]
theorem comparisonIso.app.hom.underlying
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    CategoryTheory.RelativeInertia.hom (comparisonIso.app F Z).hom =
      𝟙 ((viaTarget F).obj Z).obj := sorry
/- Proof strategy: unfold `comparisonIso.app` and use `RelativeInertia.isoMk.hom`. -/

/-- The underlying inverse arrow of the objectwise comparison is the identity. -/
@[simp, stacks 04Z6 "relative-inertia square inverse component underlying arrow"]
theorem comparisonIso.app.inv.underlying
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    CategoryTheory.RelativeInertia.hom (comparisonIso.app F Z).inv =
      𝟙 ((viaSource F).obj Z).obj := sorry
/- Proof strategy: unfold `comparisonIso.app` and use `RelativeInertia.isoMk.inv`. -/

/-- The forward component of the based relative-inertia comparison is the explicit
identity-arrow component. -/
@[simp, stacks 04Z6 "relative-inertia square packaged forward component"]
theorem comparisonIso.hom.app
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    (comparisonIso F).hom.toNatTrans.app Z = (comparisonIso.app F Z).hom := sorry
/- Proof strategy: unfold `comparisonIso` and use `BasedNatIso.ofComponents.hom.app`. -/

/-- The inverse component of the based relative-inertia comparison is the explicit
identity-arrow component in the reverse direction. -/
@[simp, stacks 04Z6 "relative-inertia square packaged inverse component"]
theorem comparisonIso.inv.app
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    (comparisonIso F).inv.toNatTrans.app Z = (comparisonIso.app F Z).inv := sorry
/- Proof strategy: unfold `comparisonIso` and use `BasedNatIso.ofComponents.inv.app`. -/

/-- The underlying arrow of every forward packaged comparison component is the identity on the
image of the source object. -/
@[simp, stacks 04Z6 "relative-inertia square packaged forward underlying arrow"]
theorem comparisonIso.hom.app.underlying
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    CategoryTheory.RelativeInertia.hom ((comparisonIso F).hom.toNatTrans.app Z) =
      𝟙 (F.toFunctor.obj Z.obj) := sorry

/-- The underlying arrow of every inverse packaged comparison component is the identity on the
image of the source object. -/
@[simp, stacks 04Z6 "relative-inertia square packaged inverse underlying arrow"]
theorem comparisonIso.inv.app.underlying
    (F : X ⥤ᵇ Y) (Z : CategoryTheory.RelativeInertia F.toFunctor) :
    CategoryTheory.RelativeInertia.hom ((comparisonIso F).inv.toNatTrans.app Z) =
      𝟙 (F.toFunctor.obj Z.obj) := sorry

end Square

end RelativeInertia

end BasedCategory
end CategoryTheory
