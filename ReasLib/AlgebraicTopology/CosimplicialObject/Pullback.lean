/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Pullback

/-!
@stack 0172

# Pointwise pullbacks of cosimplicial objects

Cosimplicial pullbacks are the specialization of the generic functor-category pointwise API.
This leaf module records the specialization without introducing a parallel owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V W : CosimplicialObject C} (a : V ⟶ U) (b : W ⟶ U)
variable [h_pointwise : Limits.FunctorCategory.HasPointwisePullback a b]
variable {k l : SimplexCategory} (h : k ⟶ l)

set_option backward.isDefEq.respectTransparency false in
/-- The generic pointwise construction supplies the canonical pullback of a fixed cospan of
cosimplicial objects.  This bridge is needed because `CosimplicialObject` is an opaque wrapper
around its functor category. -/
@[stacks 0172 "pointwise pullback of cosimplicial objects"]
public noncomputable instance (priority := low) pointwise.pullback : HasPullback a b :=
  (functorCategoryHasLimit
    (cospan
      (a : (V : SimplexCategory ⥤ C) ⟶ (U : SimplexCategory ⥤ C))
      (b : (W : SimplexCategory ⥤ C) ⟶ (U : SimplexCategory ⥤ C))) :
    HasPullback
      (a : (V : SimplexCategory ⥤ C) ⟶ (U : SimplexCategory ⥤ C))
      (b : (W : SimplexCategory ⥤ C) ⟶ (U : SimplexCategory ⥤ C)))

/- Degreewise pullbacks assemble through the generic low-priority pointwise instance. -/

/- Evaluation is identified with the degreewise pullback by the generic canonical comparison. -/

/- The generic comparison exposes both projection formulas. -/

end CategoryTheory.CosimplicialObject
