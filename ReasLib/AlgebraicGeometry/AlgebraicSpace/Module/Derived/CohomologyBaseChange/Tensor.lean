/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor.Canonical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Tensor

/-! # Tensor inheritance of geometric-point cohomology base change -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DerivedCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X : AlgebraicSpace S}

/-- Tensor base change is the canonical pullback comparison followed by covariance in the
right tensor factor. -/
def tensorBaseChangeMap (g' : X' ⟶ X) (E K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj) :
    (ModuleDerived.pullback g').obj (tensorObj E K).obj ⟶
      (tensorObj ((pullback g').obj E) K').obj :=
  (ModuleDerived.pullbackTensorIso g' E.obj K.obj).hom ≫
    (DerivedTensor.Bifunctor.Right.isoAppOf ((ModuleDerived.pullback g').obj K.obj)
      (Modules.hasDerivedTensorRightCompatible X' _) ((ModuleDerived.pullback g').obj E.obj)).hom ≫
    (DerivedTensor.Bifunctor.leftFunctor (C := X'.Modules)
      ((ModuleDerived.pullback g').obj E.obj)).map α ≫
    (tensorObjIsoBifunctor ((pullback g').obj E) K').inv

/-- The underlying tensor base-change map is the canonical tensor comparison followed by the
derived tensor of the given target morphism. -/
theorem tensorBaseChangeMap_obj (g' : X' ⟶ X) (E K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj) :
    tensorBaseChangeMap g' E K K' α =
      (ModuleDerived.pullbackTensorIso g' E.obj K.obj).hom ≫
        (DerivedTensor.Bifunctor.Right.isoAppOf ((ModuleDerived.pullback g').obj K.obj)
          (Modules.hasDerivedTensorRightCompatible X' _)
          ((ModuleDerived.pullback g').obj E.obj)).hom ≫
        (DerivedTensor.Bifunctor.leftFunctor (C := X'.Modules)
          ((ModuleDerived.pullback g').obj E.obj)).map α ≫
        (tensorObjIsoBifunctor ((pullback g').obj E) K').inv := rfl

/-- Geometric-point cohomology base change on a cartesian square is preserved by derived
tensoring with any complex with quasi-coherent cohomology. -/
theorem cohomologyBaseChange_tensor {Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj K.obj ⟶ K'.obj)
    (E : DerivedQCoh X) (hα : cohomologyBaseChangeHolds sq K K' α) :
    cohomologyBaseChangeHolds sq (tensorObj E K) (tensorObj ((pullback g').obj E) K')
      (tensorBaseChangeMap g' E K K' α) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
