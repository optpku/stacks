/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.StrictSlice
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Strict
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting along a discrete fibration

An object over a discrete fibration `G : B ⥤ C` has a structural total functor
to `B`.  This functor is itself fibred and therefore defines a fibred category
over `B`.  The canonical slice projection `Over.forget U` is one specialization;
no topology or stack condition is involved.
-/

@[expose] public section

universe uB uC vB vC

namespace CategoryTheory.FiberedCategoryOver.Slice.Restrict

open Bicategory
open scoped CategoryTheory.Bicategory

variable {B : Type uB} {C : Type uC}
variable [Category.{vB} B] [Category.{vC} C]
variable {G : B ⥤ C} [G.IsDiscreteFibration]

/-- The projection to `B` carried by an object over the discrete fibration `G`. -/
def projection
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    X.obj.total ⥤ B :=
  FiberedCategoryOver.toFunctor X.hom

namespace projection

/-- The restricted projection followed by `G` is the ambient projection to `C`. -/
theorem comp
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    projection X ⋙ G = X.obj.p := sorry

/-- The structural projection of a strict-slice object is fibred over `B`. -/
instance isFibered
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    (projection X).IsFibered := sorry

end projection

/-- Regard the structural projection of a strict-slice object as a fibred
category over `B`. -/
def obj
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    FiberedCategoryOver.{uB, vB, uB, vB} B :=
  FiberedCategoryOver.ofFunctor (projection X)

namespace obj

/-- The projection of the restricted fibred category is its structural total
functor to `B`. -/
@[simp]
theorem p
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    (obj X).p = projection X := sorry

/-- Restriction keeps the ambient total category unchanged. -/
@[simp]
theorem total
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    (obj X).total = X.obj.total := sorry

end obj

/- The non-`Prop` payload of each owner is the supplied structural total
functor. Any `sorryAx` reported below is confined to fibredness laws. -/

end CategoryTheory.FiberedCategoryOver.Slice.Restrict
