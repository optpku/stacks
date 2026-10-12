/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Setoids.Hom.OneCell
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of setoid-fibred morphisms

Underlying based-functor isomorphisms and their induced owner-level lifts.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open BasedFunctor
open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

variable {X Y : FiberedCategoryOver.Setoids C}

/-- Forget an isomorphism of setoid-fibred morphisms to the corresponding isomorphism of
underlying based functors. -/
def toBasedFunctorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toBasedFunctor F ≅ toBasedFunctor G :=
  ((toBased C).mapFunctor X Y).mapIso e

/-- The forward cell of `toBasedFunctorIso` is the underlying based natural transformation. -/
@[simp]
theorem toBasedFunctorIso.hom {F G : X ⟶ Y} (e : F ≅ G) :
    (toBasedFunctorIso e).hom = e.hom.hom := sorry

/-- The inverse cell of `toBasedFunctorIso` is the underlying based natural transformation. -/
@[simp]
theorem toBasedFunctorIso.inv {F G : X ⟶ Y} (e : F ≅ G) :
    (toBasedFunctorIso e).inv = e.inv.hom := sorry

/-- Lift an isomorphism of underlying based functors to an isomorphism of setoid-fibred
morphisms. The full-subbicategory membership contributes no additional `2`-cell data. -/
@[stacks 04Z4 "lift a based-functor isomorphism for setoid-fibred categories"]
def BasedFunctorIso.lift {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) : F ≅ G :=
  Bicategory.InducedBicategory.isoMk e

/-- The forward cell of a lifted based-functor isomorphism is the supplied forward cell. -/
@[simp]
theorem BasedFunctorIso.lift.hom {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) :
    (BasedFunctorIso.lift e).hom.hom = e.hom := sorry

/-- The inverse cell of a lifted based-functor isomorphism is the supplied inverse cell. -/
@[simp]
theorem BasedFunctorIso.lift.inv {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) :
    (BasedFunctorIso.lift e).inv.hom = e.inv := sorry

end FiberedCategoryOver.Setoids

end CategoryTheory
