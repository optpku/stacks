/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Generators
import StacksCheckRecall

@[expose] public section

/-!
@stack 09CB

# Example 14.34.7

The bracket formulas for the polynomial `A`-algebra resolution are expressed using the canonical
`FreeAlgebra.generator`; the resolution-specific formulas are owned by
`CommRingCat.Under.PolynomialResolution`.  This chapter file only recalls those statements; in
particular, no local `T`, `η`, or `ε` notation is introduced.
-/

open CategoryTheory
open CategoryTheory.CommRingCat.Under.PolynomialResolution
open Under
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

variable (A : CommRingCat.{u})
variable (B : Under A)
variable {X Y : Type u} (f : X ⟶ Y) (x : X)
variable (y : ((functor A).obj B).right)

/- The polynomial model is functorial in its variables, and the categorical free-algebra
functor agrees with it naturally. -/
#check (CommRingCat.Under.FreeAlgebra.polynomialFunctor A : Type u ⥤ Under A)
#check (CommRingCat.Under.FreeAlgebra.polynomialNatIso A :
  CommRingCat.Under.FreeAlgebra.functor A ≅
    CommRingCat.Under.FreeAlgebra.polynomialFunctor A)
#check (CommRingCat.Under.FreeAlgebra.polynomialMap_generator A f x)
#check (CommRingCat.Under.FreeAlgebra.toPolynomial_generator A X x)

/- Example 14.34.7: the comultiplication is induced by the adjunction unit. -/
@[stacks 09CB "Example 14.34.7 (comultiplication)"]
#check (comultiplication.app_eq_map_unit A B :
  (comultiplication A).app B =
    (CommRingCat.Under.FreeAlgebra.functor A).map ((adjunction A).unit.app B.right))

/- Example 14.34.7: free-algebra maps carry universal generators to universal generators. -/
@[stacks 09CB "Example 14.34.7 (naturality)"]
#check (CommRingCat.Under.FreeAlgebra.map_generator A f x :
    (CommRingCat.Under.FreeAlgebra.map A f).right
        (CommRingCat.Under.FreeAlgebra.generator A (E := X) x) =
    CommRingCat.Under.FreeAlgebra.generator A (E := Y) (f x))

/- Example 14.34.7 (1): the outer face removes a bracket. -/
@[stacks 09CB "Example 14.34.7 (1)"]
#check (face.zero.generator A B y :
  ((face A 0 (1 : Fin 2)).app B).right
    (CommRingCat.Under.FreeAlgebra.generator A y) = y)

/- Example 14.34.7 (2): the inner face applies the counit inside a bracket. -/
@[stacks 09CB "Example 14.34.7 (2)"]
#check (face.one.generator A B y :
  ((face A 0 (0 : Fin 2)).app B).right
      (CommRingCat.Under.FreeAlgebra.generator A y) =
    CommRingCat.Under.FreeAlgebra.generator A (((counit A).app B).right y))

/- Example 14.34.7 (3): the outer degeneracy adds a bracket. -/
@[stacks 09CB "Example 14.34.7 (3)"]
#check (degeneracy.zero.generator A B y :
  ((degeneracy A 1 (1 : Fin 2)).app B).right
      (CommRingCat.Under.FreeAlgebra.generator A y) =
    CommRingCat.Under.FreeAlgebra.generator A
      (CommRingCat.Under.FreeAlgebra.generator A y))

/- Example 14.34.7 (4): the inner degeneracy applies the polynomial extension of the unit. -/
@[stacks 09CB "Example 14.34.7 (4)"]
#check (degeneracy.one.generator A B y :
  ((degeneracy A 1 (0 : Fin 2)).app B).right
      (CommRingCat.Under.FreeAlgebra.generator A y) =
    CommRingCat.Under.FreeAlgebra.generator A
      (((comultiplication A).app B).right y))

end CategoryTheory.CommRingCat.Under.PolynomialResolution
