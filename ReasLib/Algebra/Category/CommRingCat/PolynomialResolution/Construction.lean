module

public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
public import ReasLib.Algebra.Category.CommRingCat.Under.Module
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Construction

/-!
# Polynomial-resolution construction

This leaf owns the free-algebra adjunction, its comonad resolution, the evaluated and forgotten
views, and the source-facing face and degeneracy maps. It does not import contraction or chain
complex consequences.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open Under
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe u

namespace CategoryTheory.CommRingCat.Under.PolynomialResolution

variable (A : CommRingCat.{u})

/-- The free `A`-algebra adjunction, represented in Mathlib by `Under A`. -/
@[stacks 09CB "free algebra adjunction"]
noncomputable abbrev adjunction := CommRingCat.Under.FreeAlgebra.adjunction A

/-- The comonad on `Under A` induced by the polynomial-algebra adjunction. -/
@[stacks 09CB "polynomial algebra comonad"]
noncomputable abbrev comonad : Comonad (Under A) := (adjunction A).toComonad

/-- The endofunctor whose positive iterates form the polynomial-algebra resolution. -/
@[stacks 09CB "polynomial resolution endofunctor"]
noncomputable abbrev functor : Under A ⥤ Under A :=
  CommRingCat.Under.FreeAlgebra.comonadFunctor A

/-- The canonical augmented simplicial endofunctor resolution on `Under A`. -/
@[stacks 08NA "polynomial augmented endofunctor resolution"]
noncomputable abbrev augmented :
    SimplicialObject.Augmented (Under A ⥤ Under A) :=
  Comonad.simplicialResolution.augmented (comonad A)

/-- The polynomial-algebra resolution, functorial in the resolved `A`-algebra. -/
@[stacks 08NA "evaluated polynomial resolution functor"]
noncomputable abbrev evaluation : Under A ⥤ SimplicialObject.Augmented (Under A) :=
  Adjunction.SimplicialResolution.eval (adjunction A)

namespace underlying

/-- The polynomial-algebra resolution after forgetting functorially to augmented simplicial
sets. -/
@[stacks 08NA "polynomial resolution underlying set functor"]
noncomputable abbrev setFunctor : Under A ⥤ SimplicialObject.Augmented (Type u) :=
  Adjunction.SimplicialResolution.postcompose.eval (adjunction A)

/-- Forgetting the evaluated polynomial resolution degreewise agrees with the canonical
postcomposed adjunction resolution. -/
@[stacks 08NA "polynomial resolution underlying-set comparison"]
theorem setFunctor_eq :
    setFunctor A =
      evaluation A ⋙ SimplicialObject.Augmented.whiskeringObj
        (Under A) (Type u) (CommRingCat.Under.FreeAlgebra.carrier A) := sorry

/-- The polynomial-algebra resolution of `B` after forgetting to an augmented simplicial set. -/
@[stacks 08NA "polynomial resolution underlying set view"]
noncomputable abbrev set (B : Under A) :
    SimplicialObject.Augmented (Type u) :=
  (setFunctor A).obj B

/-- The polynomial-algebra resolution after forgetting functorially to augmented simplicial
`A`-modules. -/
@[stacks 08NA "polynomial resolution underlying module functor"]
noncomputable abbrev moduleFunctor :
    Under A ⥤ SimplicialObject.Augmented (ModuleCat.{u} A) :=
  evaluation A ⋙ SimplicialObject.Augmented.whiskeringObj (Under A) (ModuleCat.{u} A)
    (CommRingCat.Under.forgetToModule A)

/-- Forgetting the module view degreewise recovers the underlying-set polynomial resolution. -/
@[stacks 08NA "underlying module and set polynomial-resolution compatibility"]
theorem moduleFunctor_comp_forget :
    moduleFunctor A ⋙ SimplicialObject.Augmented.whiskeringObj
        (ModuleCat.{u} A) (Type u) (CategoryTheory.forget (ModuleCat.{u} A)) =
      setFunctor A := sorry

/-- The polynomial-algebra resolution of `B` after forgetting to an augmented simplicial
`A`-module. -/
@[stacks 08NA "polynomial resolution underlying module view"]
noncomputable abbrev module (B : Under A) :
    SimplicialObject.Augmented (ModuleCat.{u} A) :=
  (moduleFunctor A).obj B

end underlying

/-- The counit of the polynomial-algebra comonad. -/
@[stacks 09CB "polynomial algebra counit"]
noncomputable abbrev counit : (functor A) ⟶ 𝟭 (Under A) := (comonad A).ε

/-- The comultiplication of the polynomial-algebra comonad. -/
@[stacks 09CB "polynomial algebra comultiplication"]
noncomputable abbrev comultiplication : functor A ⟶ functor A ⋙ functor A := (comonad A).δ

/-- The `n`-th iterated face map of the polynomial-algebra resolution. -/
@[stacks 09CB "polynomial algebra resolution face maps"]
noncomputable abbrev face (n : ℕ) (j : Fin (n + 2)) :
    IteratedEndofunctor.obj (functor A) (n + 1) ⟶
      IteratedEndofunctor.obj (functor A) n :=
  IteratedEndofunctor.face (counit A) n j

/-- The `n`-th iterated degeneracy map of the polynomial-algebra resolution. -/
@[stacks 09CB "polynomial algebra resolution degeneracy maps"]
noncomputable abbrev degeneracy (n : ℕ) (j : Fin (n + 1)) :
    IteratedEndofunctor.obj (functor A) n ⟶
      IteratedEndofunctor.obj (functor A) (n + 1) :=
  IteratedEndofunctor.degeneracy (comultiplication A) n j

/-- Degree `n` of the polynomial-algebra resolution is the `(n + 1)`-fold comonad iterate. -/
@[stacks 08NA "polynomial resolution degree formula"]
theorem evaluation.obj_eq (B : Under A) (n : ℕ) :
    ((evaluation A).obj B).left.obj (op ⦋n⦌) = (functor A) ⁺⦋n⦌.obj B := sorry

/-- The polynomial resolution, functorial in the generator type. -/
@[stacks 08NE "polynomial resolution on free-algebra generators"]
noncomputable abbrev freeResolution : Type u ⥤ SimplicialObject.Augmented (Under A) :=
  Adjunction.SimplicialResolution.precompose.eval (adjunction A)

/-- The free polynomial resolution is obtained by evaluating the polynomial resolution on the
free `A`-algebra functor. -/
@[stacks 08NE "free polynomial resolution comparison"]
theorem freeResolution_eq :
    freeResolution A =
      CommRingCat.Under.FreeAlgebra.functor A ⋙ evaluation A := sorry

end CategoryTheory.CommRingCat.Under.PolynomialResolution
