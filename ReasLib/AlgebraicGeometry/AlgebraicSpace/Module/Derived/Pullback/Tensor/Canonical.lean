/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor.Isomorphism

/-! # Tensor comparison for native derived pullback -/

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Derived pullback commutes with fixed-right derived tensor, using the native cell models. -/
def pullbackTensorIso (f : X ⟶ Y) (A B : ModuleDerived Y) :
    (pullback f).obj ((DerivedTensor.Right.functor B).obj A) ≅
      (DerivedTensor.Right.functor ((pullback f).obj B)).obj ((pullback f).obj A) :=
  (pullbackIsoTotalLeftDerived f).app ((DerivedTensor.Right.functor B).obj A) ≪≫
    DerivedQCoh.rightTensorComparisonIso f A B ≪≫
    DerivedTensor.Bifunctor.Right.isoAppOf
      ((Functor.LeftDerived.Homotopy.functor (Modules.pullback f)).obj B)
      (Modules.hasDerivedTensorRightCompatible X _)
      ((Functor.LeftDerived.Homotopy.functor (Modules.pullback f)).obj A) ≪≫
    (DerivedTensor.Bifunctor.functor (C := X.Modules)).mapIso
      (((pullbackIsoTotalLeftDerived f).app A).symm.prod
        ((pullbackIsoTotalLeftDerived f).app B).symm) ≪≫
    (DerivedTensor.Bifunctor.Right.isoAppOf ((pullback f).obj B)
      (Modules.hasDerivedTensorRightCompatible X _) ((pullback f).obj A)).symm

/-- The native tensor comparison is natural in the left tensor argument. -/
theorem pullbackTensorIso_naturality (f : X ⟶ Y) (B : ModuleDerived Y)
    {A A' : ModuleDerived Y} (a : A ⟶ A') :
    (pullback f).map ((DerivedTensor.Right.functor B).map a) ≫
        (pullbackTensorIso f A' B).hom =
      (pullbackTensorIso f A B).hom ≫
        (DerivedTensor.Right.functor ((pullback f).obj B)).map ((pullback f).map a) := sorry

/-- Native derived pullback commutes naturally with tensoring by a fixed right factor. -/
def pullbackTensorNatIso (f : X ⟶ Y) (B : ModuleDerived Y) :
    DerivedTensor.Right.functor B ⋙ pullback f ≅
      pullback f ⋙ DerivedTensor.Right.functor ((pullback f).obj B) :=
  NatIso.ofComponents (fun A ↦ pullbackTensorIso f A B)
    (fun a ↦ pullbackTensorIso_naturality f B a)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
