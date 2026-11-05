/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectTensorComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Shift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Monoidal
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import Mathlib.CategoryTheory.Localization.Prod

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory ComplexShape ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- Homotopy-level pullback and pushforward form an absolute derived adjunction pair. -/
instance modulePullbackPushforwardHasPair {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived.HasDerivedAdjunction f :=
  sorry

/-- The pointwise tensor bicomplex of two unbounded complexes of `𝒪`-modules. -/
abbrev modulesTensorBicomplex {X : AlgebraicSpace S} (K L : CochainComplex (Modules X) ℤ) :
    HomologicalComplex₂ (Modules X) (up ℤ) (up ℤ) :=
  (((curriedTensor (Modules X)).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj K).obj L

/-- Termwise module pullback of a tensor bicomplex. -/
abbrev modulesPullbackMappedTensorBicomplex {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    HomologicalComplex₂ (Modules X) (up ℤ) (up ℤ) :=
  ((Modules.pullback f).mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj (modulesTensorBicomplex K L)

/-- The tensor bicomplex of the termwise pullbacks. -/
abbrev modulesPullbackTensorBicomplexMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    HomologicalComplex₂ (Modules X) (up ℤ) (up ℤ) :=
  modulesTensorBicomplex
    (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K)
    (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj L)

/- The shared bicomplex and cochain comparisons are owned by `Pullback.Tensor`.
The declarations below use the concrete cell-model pullback; the distinct total-left-derived
presentation is exported there with the `moduleTotalDerived` prefix. -/

attribute [instance] isIso_modulesPullback_totalComparison

/-- Derived functor `Lf^*(A ⊗^L B)` in two variables. -/
noncomputable abbrev moduleDerivedTensorThenPullback
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  DerivedTensor.Bifunctor.functor (C := Modules Y) ⋙ ModuleDerived.pullback f

/-- Derived functor `Lf^*A ⊗^L Lf^*B` in two variables. -/
noncomputable abbrev moduleDerivedPullbackThenTensor
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  (ModuleDerived.pullback f).prod (ModuleDerived.pullback f) ⋙
    DerivedTensor.Bifunctor.functor (C := Modules X)

/-- Counit of `Lf^*A ⊗^L Lf^*B` against the cochain-level source `Q(f^*K ⊗ f^*L)`. -/
noncomputable def moduleDerivedPullbackThenTensorCounit
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y).prod
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
      moduleDerivedPullbackThenTensor f ⟶
    modulePullbackCochainTensorSource f where
  app KL :=
    (DerivedTensor.Bifunctor.functor (C := Modules X)).map
        (Prod.mkHom
          ((ModuleDerived.pullbackCochainCounit f).app KL.1)
          ((ModuleDerived.pullbackCochainCounit f).app KL.2)) ≫
      DerivedTensor.Bifunctor.counitAppOfQ
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj KL.1)
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj KL.2)
  naturality _ _ _ := sorry

/-- The component of `moduleDerivedPullbackThenTensorCounit` is the pair of cochain counits
followed by the two-variable derived-tensor counit. -/
theorem moduleDerivedPullbackThenTensorCounit_app
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (moduleDerivedPullbackThenTensorCounit f).app (K, L) =
      (DerivedTensor.Bifunctor.functor (C := Modules X)).map
          (Prod.mkHom
            ((ModuleDerived.pullbackCochainCounit f).app K)
            ((ModuleDerived.pullbackCochainCounit f).app L)) ≫
        DerivedTensor.Bifunctor.counitAppOfQ
          (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K)
          (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj L) :=
  sorry

/-- Counit of `Lf^*(A ⊗^L B)` against the cochain-level source `Q(f^*K ⊗ f^*L)`. -/
noncomputable def moduleDerivedTensorThenPullbackCounit
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y).prod
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
      moduleDerivedTensorThenPullback f ⟶
    modulePullbackCochainTensorSource f where
  app KL :=
    (ModuleDerived.pullback f).map (DerivedTensor.Bifunctor.counitAppOfQ KL.1 KL.2) ≫
      (ModuleDerived.pullbackCochainCounit f).app (KL.1 ⊗ KL.2) ≫
      DerivedCategory.Q.map (modulesPullback_cochainTensorComparison f KL.1 KL.2)
  naturality _ _ _ := sorry

/-- The component of `moduleDerivedTensorThenPullbackCounit` is derived pullback of the tensor
counit, followed by the cochain counit and the cochain-level pullback tensorator. -/
theorem moduleDerivedTensorThenPullbackCounit_app
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (moduleDerivedTensorThenPullbackCounit f).app (K, L) =
      (ModuleDerived.pullback f).map (DerivedTensor.Bifunctor.counitAppOfQ K L) ≫
        (ModuleDerived.pullbackCochainCounit f).app (K ⊗ L) ≫
        DerivedCategory.Q.map (modulesPullback_cochainTensorComparison f K L) :=
  sorry

/-- `Lf^*A ⊗^L Lf^*B` is a left derived functor of the cochain-level source
`Q(f^*K ⊗ f^*L)`. -/
instance moduleDerivedPullbackThenTensor_isLeftDerived
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (moduleDerivedPullbackThenTensor f).IsLeftDerivedFunctor
      (moduleDerivedPullbackThenTensorCounit f)
      ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
        (HomologicalComplex.quasiIso (Modules Y) (up ℤ))) :=
  sorry

/-- The derived comparison `Lf^*(A ⊗^L B) ⟶ Lf^*A ⊗^L Lf^*B` as a natural transformation. -/
noncomputable def moduleDerivedPullbackTensorComparisonNatTrans
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    moduleDerivedTensorThenPullback f ⟶ moduleDerivedPullbackThenTensor f :=
  (moduleDerivedPullbackThenTensor f).leftDerivedLift
    (moduleDerivedPullbackThenTensorCounit f)
    ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
      (HomologicalComplex.quasiIso (Modules Y) (up ℤ)))
    (moduleDerivedTensorThenPullback f)
    (moduleDerivedTensorThenPullbackCounit f)

/-- `moduleDerivedPullbackTensorComparisonNatTrans` is the left-derived lift of the
tensor-then-pullback counit against the pullback-then-tensor model. -/
theorem moduleDerivedPullbackTensorComparisonNatTrans_eq
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    moduleDerivedPullbackTensorComparisonNatTrans f =
      (moduleDerivedPullbackThenTensor f).leftDerivedLift
        (moduleDerivedPullbackThenTensorCounit f)
        ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
          (HomologicalComplex.quasiIso (Modules Y) (up ℤ)))
        (moduleDerivedTensorThenPullback f)
        (moduleDerivedTensorThenPullbackCounit f) :=
  sorry

/-- Ambient derived comparison `Lf^*(A ⊗^L B) ⟶ Lf^*A ⊗^L Lf^*B`. -/
noncomputable def moduleDerivedPullbackTensorComparison
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (A B : ModuleDerived Y) :
    (ModuleDerived.pullback f).obj
        ((DerivedTensor.Bifunctor.functor (C := Modules Y)).obj (A, B)) ⟶
      (DerivedTensor.Bifunctor.functor (C := Modules X)).obj
        ((ModuleDerived.pullback f).obj A, (ModuleDerived.pullback f).obj B) :=
  (moduleDerivedPullbackTensorComparisonNatTrans f).app (A, B)

/-- `moduleDerivedPullbackTensorComparison` is the component of the derived comparison
natural transformation. -/
theorem moduleDerivedPullbackTensorComparison_eq
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (A B : ModuleDerived Y) :
    moduleDerivedPullbackTensorComparison f A B =
      (moduleDerivedPullbackTensorComparisonNatTrans f).app (A, B) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
