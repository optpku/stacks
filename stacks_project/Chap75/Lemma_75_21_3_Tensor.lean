/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal

/-! # Tensor base-change compatibility -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologyBaseChange_tensor :
    ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    {Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj)
    (E : DerivedQCoh X) (hα : cohomologyBaseChangeHolds sq K K' α),
    cohomologyBaseChangeHolds sq (tensorObj E K) (tensorObj ((pullback g').obj E) K')
      (tensorBaseChangeMap g' E K K' α))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullbackTensorIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (A B : ModuleDerived Y),
    (ModuleDerived.pullback f).obj ((CategoryTheory.DerivedCategory.DerivedTensor.Right.functor B).obj A) ≅
      (CategoryTheory.DerivedCategory.DerivedTensor.Right.functor
        ((ModuleDerived.pullback f).obj B)).obj ((ModuleDerived.pullback f).obj A))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
