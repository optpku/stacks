module

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

/-- Termwise pullback of a tensor bicomplex admits a total complex. -/
instance modulesPullbackMappedTensorBicomplex_hasTotal {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (modulesPullbackMappedTensorBicomplex f K L).HasTotal (up ℤ) :=
  sorry

/-- The pointwise pullback tensor comparison commutes with the first bicomplex differential. -/
theorem modulesPullback_tensorBicomplex_comm₁ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) (i₁ i₁' i₂ : ℤ) (differentialRelation : (up ℤ).Rel i₁ i₁') :
    Modules.DirectTensorComparison.pullbackTensor f (K.X i₁) (L.X i₂) ≫
        ((modulesPullbackTensorBicomplexMap f K L).d i₁ i₁').f i₂ =
      ((modulesPullbackMappedTensorBicomplex f K L).d i₁ i₁').f i₂ ≫
        Modules.DirectTensorComparison.pullbackTensor f (K.X i₁') (L.X i₂) :=
  sorry

/-- The pointwise pullback tensor comparison commutes with the second bicomplex differential. -/
theorem modulesPullback_tensorBicomplex_comm₂ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) (i₁ i₂ i₂' : ℤ) (differentialRelation : (up ℤ).Rel i₂ i₂') :
    Modules.DirectTensorComparison.pullbackTensor f (K.X i₁) (L.X i₂) ≫
        ((modulesPullbackTensorBicomplexMap f K L).X i₁).d i₂ i₂' =
      ((modulesPullbackMappedTensorBicomplex f K L).X i₁).d i₂ i₂' ≫
        Modules.DirectTensorComparison.pullbackTensor f (K.X i₁) (L.X i₂') :=
  sorry

set_option maxRecDepth 4096 in
/-- Pointwise `f^*(M ⊗ N) ⟶ f^* M ⊗ f^* N` as a morphism of tensor bicomplexes. -/
noncomputable def modulesPullback_tensorBicomplexHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    modulesPullbackMappedTensorBicomplex f K L ⟶ modulesPullbackTensorBicomplexMap f K L :=
  HomologicalComplex₂.homMk
    (fun pq ↦ Modules.DirectTensorComparison.pullbackTensor f (K.X pq.1) (L.X pq.2))
    (modulesPullback_tensorBicomplex_comm₁ f K L)
    (modulesPullback_tensorBicomplex_comm₂ f K L)

/-- Additive-functor/total comparison for pullback of a tensor bicomplex is invertible. -/
instance isIso_modulesPullback_totalComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    IsIso
      (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
        (modulesTensorBicomplex K L) (up ℤ)) :=
  sorry

/-- Cochain-level oplax comparison `f^*(K ⊗ L) ⟶ f^* K ⊗ f^* L`. -/
noncomputable def modulesPullback_cochainTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj (K ⊗ L) ⟶
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K ⊗
        ((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj L :=
  (asIso
      (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
        (modulesTensorBicomplex K L) (up ℤ))).inv ≫
    HomologicalComplex₂.total.map (modulesPullback_tensorBicomplexHom f K L) (up ℤ)

/-- `modulesPullback_cochainTensorComparison` is the inverted total comparison followed by the
totalization of the pointwise pullback tensorator. -/
theorem modulesPullback_cochainTensorComparison_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    modulesPullback_cochainTensorComparison f K L =
      (asIso
          (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
            (modulesTensorBicomplex K L) (up ℤ))).inv ≫
        HomologicalComplex₂.total.map (modulesPullback_tensorBicomplexHom f K L) (up ℤ) :=
  sorry


/-- Underived cochain-level source `Q(f^*K ⊗ f^*L)` of the derived pullback tensor comparison. -/
noncomputable abbrev modulePullbackCochainTensorSource
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CochainComplex (Modules Y) ℤ × CochainComplex (Modules Y) ℤ ⥤ ModuleDerived X :=
  ((Modules.pullback f).mapHomologicalComplex (up ℤ)).prod
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)) ⋙
    tensor (CochainComplex (Modules X) ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)

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
