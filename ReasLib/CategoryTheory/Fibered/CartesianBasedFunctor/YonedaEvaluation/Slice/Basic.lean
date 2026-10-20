/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation

/-!
# Basic arbitrary-slice computations for cartesian Yoneda evaluation

This file owns the canonical slice fiber object and the codomain-normalized evaluation arrow.
These constructions require only a functor `p : S ⥤ C` and a cartesian based slice functor.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor
open Functor.Fiber

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace CartesianBasedFunctor.Yoneda.Slice

/-- A slice object, regarded as an object of the standard fiber of `Over.forget U` over its
domain. -/
@[stacks 0GWI "slice fiber object"]
def fiberObj {U : C} (a : Over U) :
    (Over.forget U).Fiber a.left :=
  ⟨a, rfl⟩

/-- The total-category value of the canonical slice fiber object is the original slice object. -/
@[simp, stacks 0GWI "slice fiber object readout"]
theorem fiberObj.val {U : C} (a : Over U) :
    (fiberObj a).1 = a := sorry

/-- A cartesian based functor sends the canonical arrow from a slice object to the identity slice
to a strongly cartesian arrow over the slice structure map. -/
@[stacks 0GWI "arbitrary-slice cartesian map"]
theorem map.isStronglyCartesian (p : S ⥤ C) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    p.IsStronglyCartesian a.hom
      (F.toFunctor.map (Over.mkIdTerminal.from a)) := sorry

/-- Evaluation on the canonical slice arrow, with codomain normalized to the neutral Yoneda
evaluation object. -/
@[stacks 0GWI "arbitrary-slice evaluation arrow"]
noncomputable def evaluationHom (p : S ⥤ C) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    ((F.fiberFunctor a.left).obj (fiberObj a)).1 ⟶
      ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F).1 :=
  F.toFunctor.map (Over.mkIdTerminal.from a) ≫
    eqToHom (CartesianBasedFunctor.Yoneda.evaluation.obj p U F).symm

namespace evaluationHom

/-- The codomain-normalized arbitrary-slice evaluation arrow remains strongly cartesian over the
slice structure map. -/
@[stacks 0GWI "arbitrary-slice evaluation cartesianness"]
theorem isStronglyCartesian (p : S ⥤ C) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    p.IsStronglyCartesian a.hom (evaluationHom p F a) := sorry

/-- Undoing the codomain normalization recovers the image of the canonical slice arrow. -/
@[reassoc]
theorem comp_transport (p : S ⥤ C) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    evaluationHom p F a ≫
        eqToHom (CartesianBasedFunctor.Yoneda.evaluation.obj p U F) =
      F.toFunctor.map (Over.mkIdTerminal.from a) := sorry

/-- The codomain-normalized arbitrary-slice evaluation arrow is natural in the cartesian based
functor. -/
@[reassoc]
theorem naturality (p : S ⥤ C) {U : C}
    {F G : CartesianBasedFunctor.Yoneda.hom p U} (eta : F ⟶ G)
    (a : Over U) :
    (BasedNatTrans.fiberApp eta.hom a.left (fiberObj a)).1 ≫
        evaluationHom p G a =
      evaluationHom p F a ≫
        ((CartesianBasedFunctor.Yoneda.evaluation p U).map eta).1 := sorry

/-- Evaluation on canonical slice arrows is contravariantly compatible with restriction along a
slice morphism. -/
@[reassoc]
theorem restrict (p : S ⥤ C) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) {a b : Over U}
    (phi : a ⟶ b) :
    F.toFunctor.map phi ≫ evaluationHom p F b = evaluationHom p F a := sorry

end evaluationHom

end CartesianBasedFunctor.Yoneda.Slice

end CategoryTheory

/- Data audit: `fiberObj` is canonical fiber packaging, while `evaluationHom` is the image of a
specified slice arrow followed by a deterministic equality transport. -/
