/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectTensorComparison

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Prod
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal
public import stacks_project.Chap67.Lemma_67_13_7_ProjectionFormula
public import stacks_project.Chap75.Lemma_75_5_6_Tensor
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction

/-!
# Projection formula for derived quasi-coherent complexes on algebraic spaces

The canonical comparison `Rf_* E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^* K)` is obtained by transposing
the derived pullback-tensor comparison followed by the tensor of the counit of
`Lf^* ⊣ Rf_*`. For quasi-compact quasi-separated morphisms this mate is an isomorphism on
`D_QCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.Functor
open CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Module sheaves on an algebraic space inherit the symmetric monoidal structure of the
commutative small étale ringed site. -/
@[instance_reducible]
noncomputable instance modulesSymmetricCategory (X : AlgebraicSpace S) :
    SymmetricCategory X.Modules :=
  Modules.DirectTensorComparison.symmetric X

/-- Graded objects of `𝒪_X`-modules admit totalized tensor products. -/
instance modulesHasGradedTensor (X : AlgebraicSpace S)
    (G₁ G₂ : GradedObject ℤ X.Modules) :
    GradedObject.HasTensor G₁ G₂ :=
  sorry

/-- Triple tensors of graded `𝒪_X`-modules preserve the inner coproduct in the first two
factors. -/
instance modulesHasGoodTensor₁₂ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ : GradedObject ℤ X.Modules) :
    GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ :=
  sorry

/-- Triple tensors of graded `𝒪_X`-modules preserve the inner coproduct in the last two
factors. -/
instance modulesHasGoodTensor₂₃ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ : GradedObject ℤ X.Modules) :
    GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ :=
  sorry

/-- Quadruple tensors of graded `𝒪_X`-modules satisfy the extension condition. -/
instance modulesHasTensor₄ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ G₄ : GradedObject ℤ X.Modules) :
    GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ :=
  sorry

/-- Two-variable unbounded derived tensor products exist for modules on an algebraic space. -/
instance hasDerivedTensorBifunctor (X : AlgebraicSpace S) :
    DerivedTensor.Bifunctor.Has (C := X.Modules) :=
  sorry

/-- The two-variable derived tensor is a fixed-right left-derived functor. -/
instance hasDerivedTensorRightCompatible (X : AlgebraicSpace S)
    (E : ModuleDerived X) :
    DerivedTensor.Bifunctor.Right.Compatible E :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The structure morphism `𝒪_Y ⟶ f_* 𝒪_X` as a map of underlying ring sheaves of the
commutative small étale structure sheaves. -/
noncomputable def modulesRingMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (etaleRingedSite Y (commStructureSheaf Y)).structureSheaf ⟶
      (ringPushforward f).obj
        (etaleRingedSite X (commStructureSheaf X)).structureSheaf :=
  structureSheafMap f

/-- The oplax tensor comparison `f^*(M ⊗ N) ⟶ f^* M ⊗ f^* N` of module pullback. -/
noncomputable def modulesPullbackTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (M N : Modules Y) :
    (Modules.pullback f).obj (M ⊗ N) ⟶
      (Modules.pullback f).obj M ⊗ (Modules.pullback f).obj N :=
  Modules.DirectTensorComparison.pullbackTensor f M N

/-- `modulesPullbackTensorComparison` is the Chap67 adjunct of the pushforward tensorator. -/
theorem modulesPullbackTensorComparison_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (M N : Modules Y) :
    modulesPullbackTensorComparison f M N =
      Modules.DirectTensorComparison.pullbackTensor f M N :=
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

/-- The tensor bicomplex of termwise pullbacks admits a total complex. -/
instance modulesPullbackTensorBicomplexMap_hasTotal {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (modulesPullbackTensorBicomplexMap f K L).HasTotal (up ℤ) :=
  sorry

/-- The pointwise pullback tensor comparison commutes with the first bicomplex differential. -/
theorem modulesPullback_tensorBicomplex_comm₁ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) (i₁ i₁' i₂ : ℤ) (_h : (up ℤ).Rel i₁ i₁') :
    modulesPullbackTensorComparison f (K.X i₁) (L.X i₂) ≫
        ((modulesPullbackTensorBicomplexMap f K L).d i₁ i₁').f i₂ =
      ((modulesPullbackMappedTensorBicomplex f K L).d i₁ i₁').f i₂ ≫
        modulesPullbackTensorComparison f (K.X i₁') (L.X i₂) :=
  sorry

/-- The pointwise pullback tensor comparison commutes with the second bicomplex differential. -/
theorem modulesPullback_tensorBicomplex_comm₂ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) (i₁ i₂ i₂' : ℤ) (_h : (up ℤ).Rel i₂ i₂') :
    modulesPullbackTensorComparison f (K.X i₁) (L.X i₂) ≫
        ((modulesPullbackTensorBicomplexMap f K L).X i₁).d i₂ i₂' =
      ((modulesPullbackMappedTensorBicomplex f K L).X i₁).d i₂ i₂' ≫
        modulesPullbackTensorComparison f (K.X i₁) (L.X i₂') :=
  sorry

set_option maxRecDepth 4096 in
/-- Pointwise `f^*(M ⊗ N) ⟶ f^* M ⊗ f^* N` as a morphism of tensor bicomplexes. -/
noncomputable def modulesPullback_tensorBicomplexHom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    modulesPullbackMappedTensorBicomplex f K L ⟶ modulesPullbackTensorBicomplexMap f K L :=
  HomologicalComplex₂.homMk (K := modulesPullbackMappedTensorBicomplex f K L)
    (L := modulesPullbackTensorBicomplexMap f K L)
    (fun pq ↦ modulesPullbackTensorComparison f (K.X pq.1) (L.X pq.2))
    (modulesPullback_tensorBicomplex_comm₁ f K L)
    (modulesPullback_tensorBicomplex_comm₂ f K L)

/-- Additive-functor/total comparison for pullback of a tensor bicomplex is invertible. -/
theorem isIso_modulesPullback_totalComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
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
  (@asIso _ _ _ _
      (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
        (modulesTensorBicomplex K L) (up ℤ))
      (isIso_modulesPullback_totalComparison f K L)).inv ≫
    HomologicalComplex₂.total.map (modulesPullback_tensorBicomplexHom f K L) (up ℤ)

/-- `modulesPullback_cochainTensorComparison` is the inverted total comparison followed by the
totalization of the pointwise pullback tensorator. -/
theorem modulesPullback_cochainTensorComparison_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    modulesPullback_cochainTensorComparison f K L =
      (@asIso _ _ _ _
          (HomologicalComplex₂.Total.Map.Comparison.hom (Modules.pullback f)
            (modulesTensorBicomplex K L) (up ℤ))
          (isIso_modulesPullback_totalComparison f K L)).inv ≫
        HomologicalComplex₂.total.map (modulesPullback_tensorBicomplexHom f K L) (up ℤ) :=
  sorry

/-- The cochain-level counit `Lf^*(Q K) ⟶ Q(f^* K)` of derived module pullback. -/
noncomputable def modulePullbackDerived_cochainCounit {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (K : CochainComplex (Modules Y) ℤ) :
    (modulePullbackDerived f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K) :=
  (modulePullbackDerived f).map
      ((DerivedCategory.quotientCompQhIso (Modules Y)).inv.app K) ≫
    ((modulePullbackToDerived f).totalLeftDerivedCounit
        (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
        (ModuleQis Y)).app
      ((HomotopyCategory.quotient (Modules Y) (up ℤ)).obj K) ≫
    (Homotopy.cochainIso (Modules.pullback f)).hom.app K

/-- `modulePullbackDerived_cochainCounit` is the total left-derived counit transported along
`quotientCompQhIso` and the homotopy-to-cochain comparison. -/
theorem modulePullbackDerived_cochainCounit_eq {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (K : CochainComplex (Modules Y) ℤ) :
    modulePullbackDerived_cochainCounit f K =
      (modulePullbackDerived f).map
          ((DerivedCategory.quotientCompQhIso (Modules Y)).inv.app K) ≫
        ((modulePullbackToDerived f).totalLeftDerivedCounit
            (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
            (ModuleQis Y)).app
          ((HomotopyCategory.quotient (Modules Y) (up ℤ)).obj K) ≫
        (Homotopy.cochainIso (Modules.pullback f)).hom.app K :=
  sorry

/-- Underived cochain-level source `Q(f^*K ⊗ f^*L)` of the derived pullback tensor comparison. -/
noncomputable abbrev modulePullbackCochainTensorSource {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CochainComplex (Modules Y) ℤ × CochainComplex (Modules Y) ℤ ⥤ ModuleDerived X :=
  ((Modules.pullback f).mapHomologicalComplex (up ℤ)).prod
      ((Modules.pullback f).mapHomologicalComplex (up ℤ)) ⋙
    tensor (CochainComplex (Modules X) ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ ModuleDerived X)

/-- Derived functor `Lf^*(A ⊗^L B)` in two variables. -/
noncomputable abbrev moduleDerivedTensorThenPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  DerivedTensor.Bifunctor.functor (C := Modules Y) ⋙ modulePullbackDerived f

/-- Derived functor `Lf^*A ⊗^L Lf^*B` in two variables. -/
noncomputable abbrev moduleDerivedPullbackThenTensor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ModuleDerived Y × ModuleDerived Y ⥤ ModuleDerived X :=
  (modulePullbackDerived f).prod (modulePullbackDerived f) ⋙
    DerivedTensor.Bifunctor.functor (C := Modules X)

/-- Counit of `Lf^*A ⊗^L Lf^*B` against the cochain-level source `Q(f^*K ⊗ f^*L)`. -/
noncomputable def moduleDerivedPullbackThenTensorCounit {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y).prod
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
      moduleDerivedPullbackThenTensor f ⟶
    modulePullbackCochainTensorSource f where
  app KL :=
    (DerivedTensor.Bifunctor.functor (C := Modules X)).map
        (Prod.mkHom
          (modulePullbackDerived_cochainCounit f KL.1)
          (modulePullbackDerived_cochainCounit f KL.2)) ≫
      DerivedTensor.Bifunctor.counitAppOfQ
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj KL.1)
        (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj KL.2)
  naturality _ _ _ := sorry

/-- The component of `moduleDerivedPullbackThenTensorCounit` is the pair of cochain counits
followed by the two-variable derived-tensor counit. -/
theorem moduleDerivedPullbackThenTensorCounit_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (moduleDerivedPullbackThenTensorCounit f).app (K, L) =
      (DerivedTensor.Bifunctor.functor (C := Modules X)).map
          (Prod.mkHom
            (modulePullbackDerived_cochainCounit f K)
            (modulePullbackDerived_cochainCounit f L)) ≫
        DerivedTensor.Bifunctor.counitAppOfQ
          (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj K)
          (((Modules.pullback f).mapHomologicalComplex (up ℤ)).obj L) :=
  sorry

/-- Counit of `Lf^*(A ⊗^L B)` against the cochain-level source `Q(f^*K ⊗ f^*L)`. -/
noncomputable def moduleDerivedTensorThenPullbackCounit {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y).prod
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ ModuleDerived Y) ⋙
      moduleDerivedTensorThenPullback f ⟶
    modulePullbackCochainTensorSource f where
  app KL :=
    (modulePullbackDerived f).map (DerivedTensor.Bifunctor.counitAppOfQ KL.1 KL.2) ≫
      modulePullbackDerived_cochainCounit f (KL.1 ⊗ KL.2) ≫
      DerivedCategory.Q.map (modulesPullback_cochainTensorComparison f KL.1 KL.2)
  naturality _ _ _ := sorry

/-- The component of `moduleDerivedTensorThenPullbackCounit` is derived pullback of the tensor
counit, followed by the cochain counit and the cochain-level pullback tensorator. -/
theorem moduleDerivedTensorThenPullbackCounit_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K L : CochainComplex (Modules Y) ℤ) :
    (moduleDerivedTensorThenPullbackCounit f).app (K, L) =
      (modulePullbackDerived f).map (DerivedTensor.Bifunctor.counitAppOfQ K L) ≫
        modulePullbackDerived_cochainCounit f (K ⊗ L) ≫
        DerivedCategory.Q.map (modulesPullback_cochainTensorComparison f K L) :=
  sorry

/-- `Lf^*A ⊗^L Lf^*B` is a left derived functor of the cochain-level source
`Q(f^*K ⊗ f^*L)`. -/
instance moduleDerivedPullbackThenTensor_isLeftDerived {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (moduleDerivedPullbackThenTensor f).IsLeftDerivedFunctor
      (moduleDerivedPullbackThenTensorCounit f)
      ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
        (HomologicalComplex.quasiIso (Modules Y) (up ℤ))) :=
  sorry

/-- The derived comparison `Lf^*(A ⊗^L B) ⟶ Lf^*A ⊗^L Lf^*B` as a natural transformation. -/
noncomputable def moduleDerivedPullbackTensorComparisonNatTrans {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    moduleDerivedTensorThenPullback f ⟶ moduleDerivedPullbackThenTensor f :=
  (moduleDerivedPullbackThenTensor f).leftDerivedLift
    (moduleDerivedPullbackThenTensorCounit f)
    ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
      (HomologicalComplex.quasiIso (Modules Y) (up ℤ)))
    (moduleDerivedTensorThenPullback f)
    (moduleDerivedTensorThenPullbackCounit f)

/-- `moduleDerivedPullbackTensorComparisonNatTrans` is the left-derived lift of the
tensor-then-pullback counit against the pullback-then-tensor model. -/
theorem moduleDerivedPullbackTensorComparisonNatTrans_eq {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    moduleDerivedPullbackTensorComparisonNatTrans f =
      (moduleDerivedPullbackThenTensor f).leftDerivedLift
        (moduleDerivedPullbackThenTensorCounit f)
        ((HomologicalComplex.quasiIso (Modules Y) (up ℤ)).prod
          (HomologicalComplex.quasiIso (Modules Y) (up ℤ)))
        (moduleDerivedTensorThenPullback f)
        (moduleDerivedTensorThenPullbackCounit f) :=
  sorry

/-- Ambient derived comparison `Lf^*(A ⊗^L B) ⟶ Lf^*A ⊗^L Lf^*B`. -/
noncomputable def moduleDerivedPullbackTensorComparison {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (A B : ModuleDerived Y) :
    (modulePullbackDerived f).obj
        ((DerivedTensor.Bifunctor.functor (C := Modules Y)).obj (A, B)) ⟶
      (DerivedTensor.Bifunctor.functor (C := Modules X)).obj
        ((modulePullbackDerived f).obj A, (modulePullbackDerived f).obj B) :=
  (moduleDerivedPullbackTensorComparisonNatTrans f).app (A, B)

/-- `moduleDerivedPullbackTensorComparison` is the component of the derived comparison
natural transformation. -/
theorem moduleDerivedPullbackTensorComparison_eq {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (A B : ModuleDerived Y) :
    moduleDerivedPullbackTensorComparison f A B =
      (moduleDerivedPullbackTensorComparisonNatTrans f).app (A, B) :=
  sorry

/-- Derived pullback comparison on the fixed-right tensor `Lf^*(A ⊗^L B) ⟶ Lf^* A ⊗^L Lf^* B`. -/
noncomputable def rightTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A B : ModuleDerived Y) :
    (modulePullbackDerived f).obj ((DerivedTensor.Right.functor B).obj A) ⟶
      (DerivedTensor.Right.functor ((modulePullbackDerived f).obj B)).obj
        ((modulePullbackDerived f).obj A) :=
  (modulePullbackDerived f).map (DerivedTensor.Bifunctor.Right.isoApp B A).hom ≫
    moduleDerivedPullbackTensorComparison f A B ≫
      (DerivedTensor.Bifunctor.Right.isoApp
        ((modulePullbackDerived f).obj B) ((modulePullbackDerived f).obj A)).inv

/-- `rightTensorComparison` is the two-variable derived comparison conjugated by the
fixed-right/two-variable identifications. -/
theorem rightTensorComparison_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A B : ModuleDerived Y) :
    rightTensorComparison f A B =
      (modulePullbackDerived f).map (DerivedTensor.Bifunctor.Right.isoApp B A).hom ≫
        moduleDerivedPullbackTensorComparison f A B ≫
          (DerivedTensor.Bifunctor.Right.isoApp
            ((modulePullbackDerived f).obj B) ((modulePullbackDerived f).obj A)).inv :=
  sorry

/-- The canonical projection-formula mate
`Rf_* E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^* K)` on unbounded derived modules. -/
noncomputable def leftMate {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (E : ModuleDerived X) (K : ModuleDerived Y) :
    (DerivedTensor.Right.functor K).obj ((Modules.pushforwardDerived f).obj E) ⟶
      (Modules.pushforwardDerived f).obj
        ((DerivedTensor.Right.functor ((modulePullbackDerived f).obj K)).obj E) :=
  (modulePullbackDerivedPushforwardAdjunction f).homEquiv _ _
    (rightTensorComparison f ((Modules.pushforwardDerived f).obj E) K ≫
      (DerivedTensor.Right.functor ((modulePullbackDerived f).obj K)).map
        ((modulePullbackDerivedPushforwardAdjunction f).counit.app E))

/-- Transposing `leftMate` along `Lf^* ⊣ Rf_*` recovers the derived pullback-tensor comparison
of `Rf_* E ⊗^L K` followed by the fixed-right tensor of the counit `Lf^* Rf_* E ⟶ E`. -/
theorem leftMate_spec {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (E : ModuleDerived X) (K : ModuleDerived Y) :
    ((modulePullbackDerivedPushforwardAdjunction f).homEquiv _ _).symm (leftMate f E K) =
      rightTensorComparison f ((Modules.pushforwardDerived f).obj E) K ≫
        (DerivedTensor.Right.functor ((modulePullbackDerived f).obj K)).map
          ((modulePullbackDerivedPushforwardAdjunction f).counit.app E) :=
  sorry

/-- For a quasi-compact and quasi-separated morphism of algebraic spaces, the canonical
projection-formula mate is an isomorphism on derived modules with quasi-coherent cohomology. -/
theorem isIso_projectionFormula {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedQCoh X) (K : DerivedQCoh Y) :
    IsIso (leftMate f E.obj K.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
