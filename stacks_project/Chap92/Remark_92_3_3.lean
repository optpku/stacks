/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CommRingCat.Under.PolynomialResolution hiding functor
open CommRingCat.Under.FreeAlgebra hiding adjunction
open Under
open scoped Simplicial

universe u

noncomputable section

variable (A : CommRingCat.{u}) (B : Under A)

/- Companion check: the free-forgetful adjunction of `A`-algebras slices over `B` to
adjoint functors `U ⊣ V` between `Over B` and `Over ((carrier A).obj B)`. -/
#check (CategoryTheory.Over.postAdjunctionRight (adjunction A) :
  Over.post (functor A) ⋙
      Over.map ((adjunction A).counit.app B) ⊣
    Over.post (carrier A))

/- Companion check: the sliced forgetful functor commutes with the unsliced forgetful
functor from `A`-algebras to sets. -/
#check (CategoryTheory.Over.post_forget_eq_forget_comp (carrier A) B :
  Over.post (carrier A) ⋙ Over.forget ((carrier A).obj B) =
    Over.forget B ⋙ carrier A)

namespace CategoryTheory.CommRingCat.Under
namespace PolynomialResolution

/- Companion check: the free functor square commutes after slicing over `B`. -/
#check (CategoryTheory.CommRingCat.Under.PolynomialResolution.freeOver_comp_forget A B :
  (Over.post (CommRingCat.Under.FreeAlgebra.functor A) ⋙
      Over.map ((adjunction A).counit.app B)) ⋙ Over.forget B =
    Over.forget ((CommRingCat.Under.FreeAlgebra.carrier A).obj B) ⋙
      CommRingCat.Under.FreeAlgebra.functor A)

/- Remark 92.3.3: the simplicial object `X_•` of `Over B ⥤ Over B` from Simplicial,
Section 14.34, evaluated at `Over.mk (𝟙 B)` and whiskered along `Over.forget B`, equals
the standard resolution `(evaluation A).obj B`. -/
@[stacks 08PP] #check
  (CategoryTheory.CommRingCat.Under.PolynomialResolution.forget_eval_idOver_eq_evaluation A B :
  (SimplicialObject.Augmented.whiskeringObj (Over B) (Under A) (Over.forget B)).obj
    ((Adjunction.SimplicialResolution.eval
        (Over.postAdjunctionRight (adjunction A))).obj (Over.mk (𝟙 B))) =
    (evaluation A).obj B)

end PolynomialResolution
end CategoryTheory.CommRingCat.Under
