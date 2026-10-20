module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Construction
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra

/-!
@stack 09CB

# Generator formulas for polynomial resolutions

This leaf exposes the comultiplication and low-degree face and degeneracy formulas on the
canonical free-algebra generators.
-/

@[expose] public section

open CategoryTheory
open Under

universe u

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

variable (A : CommRingCat.{u})

/-- The comultiplication is the free-algebra image of the adjunction unit. -/
@[stacks 09CB "polynomial comultiplication from the unit"]
theorem comultiplication.app_eq_map_unit (B : Under A) :
    (comultiplication A).app B =
      (CommRingCat.Under.FreeAlgebra.functor A).map ((adjunction A).unit.app B.right) := sorry

/-- The first face map removes the outer bracket on a universal generator. -/
@[simp, stacks 09CB "face zero on generators"]
theorem face.zero.generator
    (B : Under A) (x : (functor A).obj B |>.right) :
    ((face A 0 (1 : Fin 2)).app B).right
        (CommRingCat.Under.FreeAlgebra.generator A x) = x := sorry

/-- The second face map applies the counit inside the outer generator. -/
@[simp, stacks 09CB "face one on generators"]
theorem face.one.generator
    (B : Under A) (x : (functor A).obj B |>.right) :
    ((face A 0 (0 : Fin 2)).app B).right
        (CommRingCat.Under.FreeAlgebra.generator A x) =
      CommRingCat.Under.FreeAlgebra.generator A (((counit A).app B).right x) := sorry

/-- The first degeneracy adds an outer free-algebra generator. -/
@[simp, stacks 09CB "degeneracy zero on generators"]
theorem degeneracy.zero.generator
    (B : Under A) (x : (functor A).obj B |>.right) :
    ((degeneracy A 1 (1 : Fin 2)).app B).right
        (CommRingCat.Under.FreeAlgebra.generator A x) =
      CommRingCat.Under.FreeAlgebra.generator A
        (CommRingCat.Under.FreeAlgebra.generator A x) := sorry

/-- The second degeneracy applies the polynomial extension of the unit before adding an outer
free-algebra generator. -/
@[simp, stacks 09CB "degeneracy one on generators"]
theorem degeneracy.one.generator
    (B : Under A) (x : (functor A).obj B |>.right) :
    ((degeneracy A 1 (0 : Fin 2)).app B).right
        (CommRingCat.Under.FreeAlgebra.generator A x) =
      CommRingCat.Under.FreeAlgebra.generator A
        (((comultiplication A).app B).right x) := sorry

end CategoryTheory.CommRingCat.Under.PolynomialResolution
