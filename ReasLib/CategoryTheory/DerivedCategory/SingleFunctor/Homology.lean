/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The degree-`b` homology of the shift by `-b` of a single object is canonically that object. -/
noncomputable def homologyShiftedSingleIso (F : C) (b : ℤ) :
    (_root_.DerivedCategory.homologyFunctor C b).obj
      ((_root_.DerivedCategory.singleFunctor C 0).obj F⟦-b⟧) ≅ F :=
  ((_root_.DerivedCategory.homologyFunctor C 0).shiftIso (-b) b 0
      (neg_add_cancel b)).app ((_root_.DerivedCategory.singleFunctor C 0).obj F) ≪≫
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app F

/-- The homology morphism induced by a map from a shifted single object, transported along
the canonical homology isomorphism. -/
noncomputable def homologyMapOfShiftedSingle
    {F : C} {K : DerivedCategory C} {b : ℤ}
    (φ : (_root_.DerivedCategory.singleFunctor C 0).obj F⟦-b⟧ ⟶ K) :
    F ⟶ (_root_.DerivedCategory.homologyFunctor C b).obj K :=
  (homologyShiftedSingleIso C F b).inv ≫
    (_root_.DerivedCategory.homologyFunctor C b).map φ

/-- The induced homology morphism is the composite of the inverse canonical homology
isomorphism with the homology functor's image of the supplied morphism. -/
theorem homologyMapOfShiftedSingle_eq
    {F : C} {K : DerivedCategory C} {b : ℤ}
    (φ : (_root_.DerivedCategory.singleFunctor C 0).obj F⟦-b⟧ ⟶ K) :
    homologyMapOfShiftedSingle C φ =
      (homologyShiftedSingleIso C F b).inv ≫
        (_root_.DerivedCategory.homologyFunctor C b).map φ := rfl

end CategoryTheory.DerivedCategory
