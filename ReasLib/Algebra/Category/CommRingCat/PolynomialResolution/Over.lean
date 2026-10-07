module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction

@[expose] public section

open CategoryTheory
open CommRingCat.Under.PolynomialResolution
open CommRingCat.Under.FreeAlgebra
open Under
open scoped Simplicial

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

variable (A : CommRingCat.{u}) (B : Under A)

/-- Slicing the free-algebra adjunction over `B` commutes with forgetting to the free algebra. -/
theorem freeOver_comp_forget :
    (Over.post (CommRingCat.Under.FreeAlgebra.functor A) ⋙
        Over.map ((adjunction A).counit.app B)) ⋙ Over.forget B =
      Over.forget ((CommRingCat.Under.FreeAlgebra.carrier A).obj B) ⋙
        CommRingCat.Under.FreeAlgebra.functor A := sorry

/-- Forgetting the sliced simplicial resolution at the identity of `B` gives the evaluated
polynomial resolution of `B`. -/
theorem forget_eval_idOver_eq_evaluation :
    (SimplicialObject.Augmented.whiskeringObj (Over B) (Under A) (Over.forget B)).obj
      ((Adjunction.SimplicialResolution.eval
          (Over.postAdjunctionRight (adjunction A))).obj (Over.mk (𝟙 B))) =
      (evaluation A).obj B := sorry

end CategoryTheory.CommRingCat.Under.PolynomialResolution
