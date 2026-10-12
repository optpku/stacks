/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Basic

/-!
# Basic arbitrary-slice computations for fibered Yoneda evaluation

This file is the fixed-universe adapter for the neutral arbitrary-slice evaluation arrow. The
canonical slice fiber object remains owned by `CartesianBasedFunctor.Yoneda.Slice`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Functor
open Functor.Fiber
open FiberedCategoryOver
open CartesianBasedFunctor.Yoneda.Slice (fiberObj)

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.YonedaSlice

variable (X : FiberedCategoryOver C)

/-- A morphism of fibred categories sends the canonical slice arrow to a strongly cartesian arrow
over the underlying slice morphism. -/
theorem map.isStronglyCartesian {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    X.p.IsStronglyCartesian a.hom
      ((toFunctor F).map (Over.mkIdTerminal.from a)) := sorry

/-- Evaluation of `F` on the canonical slice arrow, with its codomain normalized to the underlying
object of `YonedaSlice.evaluation`. This is the preferred total-category readout when comparing
with a cartesian lift. -/
@[stacks 0GWI "bundled arbitrary-slice Yoneda evaluation arrow"]
noncomputable def evaluationHom {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    ((fiberFunctor F a.left).obj (fiberObj a)).1 ⟶
      ((evaluation X U).obj F).1 :=
  CartesianBasedFunctor.Yoneda.Slice.evaluationHom X.p
    (FiberedCategoryOver.toCartesianBasedFunctor F) a

namespace evaluationHom

/-- The codomain-normalized slice-evaluation arrow remains strongly cartesian over the slice
structure morphism. -/
theorem isStronglyCartesian {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    X.p.IsStronglyCartesian a.hom (evaluationHom X F a) := sorry

/-- Undoing the codomain normalization of the arbitrary-slice evaluation arrow recovers the
actual image of the canonical slice arrow. -/
@[reassoc]
theorem comp_transport {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    evaluationHom X F a ≫ eqToHom (evaluation.obj X U F) =
      (toFunctor F).map (Over.mkIdTerminal.from a) := sorry

/-- The codomain-normalized arbitrary-slice evaluation arrow is natural in the morphism of
fibred categories. -/
@[reassoc]
theorem naturality {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X}
    (η : F ⟶ G) (a : Over U) :
    (BasedNatTrans.fiberApp η.hom a.left (fiberObj a)).1 ≫ evaluationHom X G a =
      evaluationHom X F a ≫ ((evaluation X U).map η).1 := sorry

/-- Evaluation on canonical slice arrows is compatible with restriction along a slice morphism. -/
@[reassoc]
theorem restrict {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X)
    {a b : Over U} (φ : a ⟶ b) :
    (toFunctor F).map φ ≫ evaluationHom X F b = evaluationHom X F a := sorry

end evaluationHom

end FiberedCategoryOver.YonedaSlice

end CategoryTheory

/- Data audit: `evaluationHom` delegates its non-Prop payload to the neutral cartesian based
functor owner. Deferred axioms occur only in cartesianness and equality statements. -/
