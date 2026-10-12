/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectTensorComparison

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Source
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_13_7_ProjectionFormula
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap86.«86_3_2_1_Pushforward»

/-!
# Derived pullback, tensor, and the structure sheaf on `DerivedQCoh`

This module lifts unbounded derived pullback of module sheaves on algebraic spaces to
complexes with quasi-coherent cohomology, and records the derived structure sheaf together
with the fixed-right derived tensor product on `DerivedQCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory ObjectProperty
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- Module sheaves on an algebraic space inherit the canonical tensor product of the commutative
small étale ringed site. -/
@[instance_reducible]
noncomputable instance modulesMonoidalCategory (X : AlgebraicSpace S) :
    MonoidalCategory (Modules X) :=
  Modules.instMonoidalCategory X

/-- The tensor product of `𝒪_X`-modules is additive in each variable. -/
instance modulesMonoidalPreadditive (X : AlgebraicSpace S) :
    MonoidalPreadditive (Modules X) :=
  sorry

/-- Totalized tensor products of unbounded complexes of `𝒪_X`-modules exist. -/
instance modulesHasMapBifunctor (X : AlgebraicSpace S)
    (K L : CochainComplex (Modules X) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (MonoidalCategory.curriedTensor (Modules X)) (up ℤ) :=
  sorry

/-- Fixed-right unbounded derived tensor products exist for modules on an algebraic space. -/
instance hasDerivedTensorRight (X : AlgebraicSpace S) :
    DerivedTensor.Right.Has (C := Modules X) :=
  sorry

/-- Module sheaves on an algebraic space inherit the symmetric monoidal structure of the
commutative small étale ringed site. -/
@[instance_reducible]
noncomputable instance modulesSymmetricCategory (X : AlgebraicSpace S) :
    SymmetricCategory (Modules X) :=
  Modules.DirectTensorComparison.symmetric X

/-- Graded objects of `𝒪_X`-modules admit totalized tensor products. -/
instance modulesHasGradedTensor (X : AlgebraicSpace S)
    (G₁ G₂ : GradedObject ℤ (Modules X)) :
    GradedObject.HasTensor G₁ G₂ :=
  sorry

/-- Triple tensors of graded `𝒪_X`-modules preserve the inner coproduct in the first two
factors. -/
instance modulesHasGoodTensor₁₂ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ : GradedObject ℤ (Modules X)) :
    GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ :=
  sorry

/-- Triple tensors of graded `𝒪_X`-modules preserve the inner coproduct in the last two
factors. -/
instance modulesHasGoodTensor₂₃ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ : GradedObject ℤ (Modules X)) :
    GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ :=
  sorry

/-- Quadruple tensors of graded `𝒪_X`-modules satisfy the extension condition. -/
instance modulesHasTensor₄ (X : AlgebraicSpace S)
    (G₁ G₂ G₃ G₄ : GradedObject ℤ (Modules X)) :
    GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ :=
  sorry

/-- Two-variable unbounded derived tensor products exist for modules on an algebraic space. -/
instance hasDerivedTensorBifunctor (X : AlgebraicSpace S) :
    DerivedTensor.Bifunctor.Has (C := Modules X) :=
  sorry

/-- The two-variable derived tensor is a fixed-right left-derived functor. -/
instance hasDerivedTensorRightCompatible (X : AlgebraicSpace S)
    (E : ModuleDerived X) :
    DerivedTensor.Bifunctor.Right.Compatible E :=
  sorry

/-- Quasi-coherent cohomology is a triangulated subcategory of `D(𝒪_X)`. -/
instance derivedQuasiCoherent_isTriangulated (X : AlgebraicSpace S) :
    (derivedQuasiCoherentModuleProperty X).IsTriangulated :=
  sorry

namespace pullback

/-- Derived pullback along a morphism of algebraic spaces preserves quasi-coherent cohomology. -/
theorem mapsTo {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage (modulePullbackDerived f) :=
  sorry

end pullback

/-- Derived pullback `Lf^*` along a morphism of algebraic spaces, restricted to complexes with
quasi-coherent cohomology. -/
noncomputable def pullback {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    DerivedQCoh X ⥤ DerivedQCoh Y :=
  (derivedQuasiCoherentModuleProperty Y).lift
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ modulePullbackDerived f)
    (fun E ↦ pullback.mapsTo f E.obj E.property)

/-- Forgetting the quasi-coherent lift of derived pullback recovers ambient derived pullback. -/
noncomputable def pullback.inclusionIso {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    pullback f ⋙ (derivedQuasiCoherentModuleProperty Y).ι ≅
      (derivedQuasiCoherentModuleProperty X).ι ⋙ modulePullbackDerived f :=
  (derivedQuasiCoherentModuleProperty Y).liftCompιIso
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ modulePullbackDerived f)
    (fun E ↦ pullback.mapsTo f E.obj E.property)

/-- The underlying derived module of restricted pullback is ambient derived pullback. -/
@[simp]
theorem pullback.obj_obj {Y X : AlgebraicSpace S} (f : Y ⟶ X) (E : DerivedQCoh X) :
    ((pullback f).obj E).obj = (modulePullbackDerived f).obj E.obj :=
  sorry

/-- The structure sheaf placed in degree zero has quasi-coherent cohomology. -/
theorem structureSheaf_mem (X : AlgebraicSpace S) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedCategory.singleFunctor (Modules X) 0).obj
        (tensorUnit (Modules X))) :=
  sorry

/-- The structure sheaf `𝒪_X`, placed in degree zero, as a derived module with quasi-coherent
cohomology. This is the tensor unit of `Modules X`, the canonical owner of `K ⊗^L 𝒪_X`. -/
noncomputable def structureSheaf (X : AlgebraicSpace S) : DerivedQCoh X :=
  ⟨(DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X)),
    structureSheaf_mem X⟩

/-- The underlying derived module of the derived structure sheaf is the tensor unit placed in
degree zero. -/
theorem structureSheaf_obj (X : AlgebraicSpace S) :
    (structureSheaf X).obj =
      (DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X)) :=
  sorry

/-- The derived structure sheaf is canonically the degree-zero placement of the module tensor
unit. -/
noncomputable def structureSheafUnitIso (X : AlgebraicSpace S) :
    (structureSheaf X).obj ≅
      (DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X)) where
  hom := 𝟙 _
  inv := 𝟙 _

/-- The forward map of `structureSheafUnitIso` is the identity comparison of the degree-zero
unit complex. -/
theorem structureSheafUnitIso_hom (X : AlgebraicSpace S) :
    (structureSheafUnitIso X).hom = 𝟙 (structureSheaf X).obj :=
  sorry

namespace tensorRight

/-- Fixed-right derived tensor preserves derived modules with quasi-coherent cohomology. -/
theorem mapsTo {X : AlgebraicSpace S} (L : DerivedQCoh X) :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty X).inverseImage
        (DerivedTensor.Right.functor L.obj) :=
  sorry

end tensorRight

/-- Fixed-right derived tensor `- ⊗^L L`, restricted to complexes with quasi-coherent
cohomology. -/
noncomputable def tensorRight {X : AlgebraicSpace S} (L : DerivedQCoh X) :
    DerivedQCoh X ⥤ DerivedQCoh X :=
  (derivedQuasiCoherentModuleProperty X).lift
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ DerivedTensor.Right.functor L.obj)
    (fun K ↦ tensorRight.mapsTo L K.obj K.property)

/-- Forgetting the quasi-coherent lift of fixed-right derived tensor recovers ambient derived
tensor. -/
noncomputable def tensorRight.inclusionIso {X : AlgebraicSpace S} (L : DerivedQCoh X) :
    tensorRight L ⋙ (derivedQuasiCoherentModuleProperty X).ι ≅
      (derivedQuasiCoherentModuleProperty X).ι ⋙ DerivedTensor.Right.functor L.obj :=
  (derivedQuasiCoherentModuleProperty X).liftCompιIso
    ((derivedQuasiCoherentModuleProperty X).ι ⋙ DerivedTensor.Right.functor L.obj)
    (fun K ↦ tensorRight.mapsTo L K.obj K.property)

/-- The derived tensor product of two complexes with quasi-coherent cohomology. -/
noncomputable def tensorObj {X : AlgebraicSpace S} (K L : DerivedQCoh X) : DerivedQCoh X :=
  (tensorRight L).obj K

/-- The underlying derived module of a restricted tensor object is the ambient fixed-right
derived tensor. -/
@[simp]
theorem tensorObj_obj {X : AlgebraicSpace S} (K L : DerivedQCoh X) :
    (tensorObj K L).obj = (DerivedTensor.Right.functor L.obj).obj K.obj :=
  sorry

/-- The restricted tensor object compares with the two-variable derived tensor bifunctor. -/
noncomputable def tensorObjIsoBifunctor {X : AlgebraicSpace S} (K L : DerivedQCoh X) :
    (tensorObj K L).obj ≅
      (DerivedTensor.Bifunctor.functor (C := Modules X)).obj (K.obj, L.obj) :=
  DerivedTensor.Bifunctor.Right.isoApp L.obj K.obj

/-- Functoriality of `tensorObj` in the right factor, via the two-variable derived tensor. -/
noncomputable def tensorMapRight {X : AlgebraicSpace S} (K : DerivedQCoh X)
    {L L' : DerivedQCoh X} (g : L ⟶ L') :
    tensorObj K L ⟶ tensorObj K L' :=
  ObjectProperty.homMk <|
    (tensorObjIsoBifunctor K L).hom ≫
      (DerivedTensor.Bifunctor.leftFunctor (C := Modules X) K.obj).map g.hom ≫
        (tensorObjIsoBifunctor K L').inv

/-- Degree-zero placement of the module tensor unit. -/
noncomputable def derivedTensorUnit (X : AlgebraicSpace S) : ModuleDerived X :=
  (DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X))

/-- `derivedTensorUnit` is the degree-zero placement of the module tensor unit. -/
theorem derivedTensorUnit_eq (X : AlgebraicSpace S) :
    derivedTensorUnit X =
      (DerivedCategory.singleFunctor (Modules X) 0).obj (tensorUnit (Modules X)) :=
  sorry

/-- The cochain-level right unitor `K ⊗ 𝟙 ⟶ K`, viewed in `D(𝒪_X)`. -/
noncomputable def derivedTensorRightUnitor {X : AlgebraicSpace S} (K : ModuleDerived X) :
    (DerivedTensor.Bifunctor.functor (C := Modules X)).obj (K, derivedTensorUnit X) ⟶ K :=
  (DerivedTensor.Bifunctor.functor (C := Modules X)).map
      (CategoryTheory.Prod.mkHom (DerivedCategory.Q.objObjPreimageIso K).inv
        (𝟙 (derivedTensorUnit X))) ≫
    DerivedTensor.Bifunctor.counitAppOfQ (DerivedCategory.Q.objPreimage K)
      (tensorUnit (CochainComplex (Modules X) ℤ)) ≫
    DerivedCategory.Q.map (MonoidalCategory.rightUnitor
      (DerivedCategory.Q.objPreimage K)).hom ≫
    (DerivedCategory.Q.objObjPreimageIso K).hom

/-- `derivedTensorRightUnitor` is the cochain right unitor transported to the derived category. -/
theorem derivedTensorRightUnitor_eq {X : AlgebraicSpace S} (K : ModuleDerived X) :
    derivedTensorRightUnitor K =
      (DerivedTensor.Bifunctor.functor (C := Modules X)).map
          (CategoryTheory.Prod.mkHom (DerivedCategory.Q.objObjPreimageIso K).inv
            (𝟙 (derivedTensorUnit X))) ≫
        DerivedTensor.Bifunctor.counitAppOfQ (DerivedCategory.Q.objPreimage K)
          (tensorUnit (CochainComplex (Modules X) ℤ)) ≫
        DerivedCategory.Q.map (MonoidalCategory.rightUnitor
          (DerivedCategory.Q.objPreimage K)).hom ≫
        (DerivedCategory.Q.objObjPreimageIso K).hom :=
  sorry

/-- The right unitor `K ⊗^L 𝒪_X ⟶ K` obtained by identifying the derived structure sheaf with
the degree-zero tensor unit and applying the cochain unitor. -/
noncomputable def tensorUnitor {X : AlgebraicSpace S} (K : DerivedQCoh X) :
    tensorObj K (structureSheaf X) ⟶ K :=
  ObjectProperty.homMk <|
    (tensorObjIsoBifunctor K (structureSheaf X)).hom ≫
      derivedTensorRightUnitor K.obj

/-- The underlying morphism of `tensorUnitor` is the cochain right unitor on the derived tensor
unit. -/
theorem tensorUnitor_eq {X : AlgebraicSpace S} (K : DerivedQCoh X) :
    (tensorUnitor K).hom =
      (tensorObjIsoBifunctor K (structureSheaf X)).hom ≫
        derivedTensorRightUnitor K.obj :=
  sorry

/-- Module pushforward along a morphism of algebraic spaces is additive. -/
instance modulesPushforward_additive {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (Modules.pushforward f).Additive :=
  sorry

/-- Homotopy-to-derived module pullback admits a total left derived functor. -/
instance modulePullbackToDerived_hasLeftDerived {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((Modules.pullback f).mapHomotopyCategory (up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X)).HasLeftDerivedFunctor
      (ModuleQis Y) :=
  (instModulePullbackToDerivedHasLeftDerivedFunctor f :
    (modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis Y))

/-- Homotopy-to-derived module pushforward admits a total right derived functor. -/
instance modulePushforwardToDerived_hasRightDerived {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((Modules.pushforward f).mapHomotopyCategory (up ℤ) ⋙
        (DerivedCategory.Qh : HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)).HasRightDerivedFunctor
      (ModuleQis X) :=
  Functor.RightDerived.KInjective.hasDerived (Modules.pushforward f)

/-- Homotopy-level pullback and pushforward form an absolute derived adjunction pair. -/
instance modulePullbackPushforwardHasPair {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Adjunction.TotalDerived.HasPair
      (G := (Modules.pullback f).mapHomotopyCategory (up ℤ))
      (F := (Modules.pushforward f).mapHomotopyCategory (up ℤ))
      (ModuleQis Y) (ModuleQis X)
      (L1 := DerivedCategory.Qh) (L2 := DerivedCategory.Qh) :=
  sorry

/-- The unbounded derived adjunction `Lf^* ⊣ Rf_*` on `D(𝒪)`. -/
noncomputable def modulePullbackDerivedPushforwardAdjunction
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    modulePullbackDerived f ⊣ Modules.pushforwardDerived f :=
  Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction f))
    (ModuleQis Y) (ModuleQis X)

/-- The derived adjunction `Lf^* ⊣ Rf_*` is the total-derived adjunction of homotopy-level
module pullback and pushforward. -/
theorem modulePullbackDerivedPushforwardAdjunction_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    modulePullbackDerivedPushforwardAdjunction f =
      Adjunction.TotalDerived.HasPair.derived
        (Adjunction.mapHomotopyCategoryAdjunction (Modules.pullbackPushforwardAdjunction f))
        (ModuleQis Y) (ModuleQis X) :=
  sorry

/-- Restricted derived pullback is left adjoint to restricted derived pushforward on complexes
with quasi-coherent cohomology. -/
noncomputable def pullbackPushforwardCohomologyAdjunction {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pullback f ⊣ pushforwardCohomologyIn f :=
  ObjectProperty.FullSubcategory.adjunction
    (modulePullbackDerived f) (Modules.pushforwardDerived f)
    (modulePullbackDerivedPushforwardAdjunction f)
    (pullback.mapsTo f) (pushforwardCohomologyIn.mapsTo f)

/-- `pullbackPushforwardCohomologyAdjunction` is the object-property restriction of the ambient
derived adjunction. -/
theorem pullbackPushforwardCohomologyAdjunction_eq {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pullbackPushforwardCohomologyAdjunction f =
      ObjectProperty.FullSubcategory.adjunction
        (modulePullbackDerived f) (Modules.pushforwardDerived f)
        (modulePullbackDerivedPushforwardAdjunction f)
        (pullback.mapsTo f) (pushforwardCohomologyIn.mapsTo f) :=
  sorry

/-- The structure morphism `𝒪_Y ⟶ f_* 𝒪_X` as a map of underlying ring sheaves of the
commutative small étale structure sheaves. -/
noncomputable def modulesRingMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (etaleRingedSite Y (commStructureSheaf Y)).structureSheaf ⟶
      (ringPushforward f).obj
        (etaleRingedSite X (commStructureSheaf X)).structureSheaf :=
  structureSheafMap f

/-- The lax tensor comparison `f_* P ⊗ f_* Q ⟶ f_*(P ⊗ Q)` of module pushforward. -/
noncomputable def modulesPushforward_μ {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P Q : Modules X) :
    (Modules.pushforward f).obj P ⊗ (Modules.pushforward f).obj Q ⟶
      (Modules.pushforward f).obj (P ⊗ Q) :=
  Modules.DirectTensorComparison.pushforwardTensor f P Q

/-- `modulesPushforward_μ` is the Chap67 bilinear comparison. -/
theorem modulesPushforward_μ_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P Q : Modules X) :
    modulesPushforward_μ f P Q =
      Modules.DirectTensorComparison.pushforwardTensor f P Q :=
  sorry

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

/-- The module-level pullback tensor comparison is an isomorphism. -/
theorem isIso_modulesPullbackTensorComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (M N : Modules Y) :
    IsIso (modulesPullbackTensorComparison f M N) :=
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
  HomologicalComplex₂.homMk
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

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
