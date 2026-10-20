/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universe-polymorphic cartesian Yoneda evaluation

This neutral leaf owns only the cartesian slice-functor category and evaluation at the identity
slice object. It assumes neither a cleavage nor a bundled fixed-universe fibred-category owner.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor
open Functor.Fiber

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace CartesianBasedFunctor.Yoneda

/-- The category of cartesian based functors from the slice projection `C/U` to `p : S ⥤ C`.

Unlike a hom-category in a fixed `FiberedCategoryOver` bicategory, this owner allows the total
category `S` and the slice category to occupy unrelated universes. -/
@[stacks 0GWI "universe-polymorphic cartesian Yoneda hom"]
abbrev hom (p : S ⥤ C) (U : C) :=
  CartesianBasedFunctor (Over.forget U) p

/-- Evaluation of a cartesian slice functor at the identity object `𝟙 U`, valued in `p.Fiber U`.

This is restriction of the neutral based evaluation along the forgetful functor from cartesian
based functors. -/
@[stacks 0GWI "universe-polymorphic cartesian Yoneda evaluation"]
noncomputable def evaluation (p : S ⥤ C) (U : C) : hom p U ⥤ p.Fiber U :=
  CartesianBasedFunctor.forget (Over.forget U) p ⋙
    BasedCategory.Yoneda.evaluation p U

namespace evaluation

/-- On objects, cartesian Yoneda evaluation is evaluation of the underlying total functor at
`Over.mk (𝟙 U)`. -/
@[simp, stacks 0GWI "cartesian Yoneda object readout"]
theorem obj (p : S ⥤ C) (U : C) (F : hom p U) :
    (fiberInclusion : p.Fiber U ⥤ S).obj ((evaluation p U).obj F) =
      F.toFunctor.obj (Over.mk (𝟙 U)) := sorry

/-- On morphisms, cartesian Yoneda evaluation is the component of the underlying vertical natural
transformation at `Over.mk (𝟙 U)`. -/
@[simp, stacks 0GWI "cartesian Yoneda morphism readout"]
theorem map (p : S ⥤ C) (U : C) {F G : hom p U} (eta : F ⟶ G) :
    (fiberInclusion : p.Fiber U ⥤ S).map ((evaluation p U).map eta) =
      eta.hom.toNatTrans.app (Over.mk (𝟙 U)) := sorry

end evaluation

end CartesianBasedFunctor.Yoneda

end CategoryTheory
