/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.MapIdentity
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

/-! # Derived pullback along the identity of an algebraic space -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}

/-- Homotopy-to-derived pullback along `𝟙 Y` is the derived localization functor. -/
@[no_expose] def homotopyPullbackIdIso (Y : AlgebraicSpace S) :
    (Modules.pullback (𝟙 Y)).mapHomotopyCategory (up ℤ) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory Y.Modules (up ℤ) ⥤ ModuleDerived Y) ≅
      (DerivedCategory.Qh :
        HomotopyCategory Y.Modules (up ℤ) ⥤ ModuleDerived Y) :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (modulesPullbackId Y) ≪≫
        Functor.mapHomotopyCategoryIdIso Y.Modules)
      DerivedCategory.Qh ≪≫
    Functor.leftUnitor _

/-- The exact derived identity functor factors homotopy pullback along the identity. -/
@[no_expose] def pullbackIdFactors (Y : AlgebraicSpace S) :
    (DerivedCategory.Qh :
      HomotopyCategory Y.Modules (up ℤ) ⥤ ModuleDerived Y) ⋙
        (ExactFunctor.id Y.Modules).mapDerivedCategory ≅
      Functor.Homotopy.toDerived (Modules.pullback (𝟙 Y)) :=
  (𝟭 Y.Modules).mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryIdIso Y.Modules) DerivedCategory.Qh ≪≫
    Functor.leftUnitor _ ≪≫ (homotopyPullbackIdIso Y).symm

/-- The exact identity factorization satisfies the left-derived universal property. -/
theorem pullbackId_model_isLeftDerived (Y : AlgebraicSpace S) :
    (ExactFunctor.id Y.Modules).mapDerivedCategory.IsLeftDerivedFunctor
      (pullbackIdFactors Y).hom (HomotopyCategory.quasiIso Y.Modules (up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (pullbackIdFactors Y)

/-- Pullback along the identity has a left derived functor given by the exact identity model. -/
theorem pullbackId_hasLeftDerived (Y : AlgebraicSpace S) :
    (Functor.Homotopy.toDerived (Modules.pullback (𝟙 Y))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso Y.Modules (up ℤ)) := by
  -- Local instance justification (proof-local temporary data): certify the explicit identity model.
  letI := pullbackId_model_isLeftDerived Y
  exact Functor.HasLeftDerivedFunctor.mk'
    (ExactFunctor.id Y.Modules).mapDerivedCategory (pullbackIdFactors Y).hom
    (W := HomotopyCategory.quasiIso Y.Modules (up ℤ))

/-- Compare the canonical cell-model pullback directly with the exact identity model
through their specified universal properties, then use the native exact-derived identity. -/
def pullbackId (Y : AlgebraicSpace S) :
    ModuleDerived.pullback (𝟙 Y) ≅ 𝟭 (ModuleDerived Y) := by
  -- Local instance justification (proof-local temporary data): certify the exact identity model alongside the specified canonical cell-model counit.
  letI := pullbackId_model_isLeftDerived Y
  exact Functor.leftDerivedUnique
    (LF := ModuleDerived.pullback (𝟙 Y))
    (LF' := (ExactFunctor.id Y.Modules).mapDerivedCategory)
    (α := ModuleDerived.pullbackCounit (𝟙 Y))
    (α'₂ := (pullbackIdFactors Y).hom)
    (W := HomotopyCategory.quasiIso Y.Modules (up ℤ)) ≪≫
    ExactFunctor.MapDerivedCategory.idFunctorIso Y.Modules

/-- The identity comparison carries the exact identity factorization to the pullback counit. -/
theorem pullbackId_fac (Y : AlgebraicSpace S) :
    Functor.whiskerLeft (DerivedCategory.Qh (C := Y.Modules))
        ((pullbackId Y ≪≫ (ExactFunctor.MapDerivedCategory.idFunctorIso Y.Modules).symm).hom) ≫
      (pullbackIdFactors Y).hom = pullbackCounit (𝟙 Y) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
