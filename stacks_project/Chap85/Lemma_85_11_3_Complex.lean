module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import stacks_project.Chap85.Lemma_85_4_2_MorphismDiagram
public import stacks_project.Chap85.Lemma_85_11_2_Complex

/-!
# Augmentation Čech cochain of an `O`-module along an induced ringed morphism

In Situation 85.3.3 case A, with an augmentation towards a site `D` as in
Remark 85.4.1 and a ring map `O_D ⟶ a_* O`, an `O`-module `F` on `C_total`
determines the cosimplicial sheaf of `O_D`-modules `n ↦ a_{n,*} F_n`, the
unaugmented alternating-coface complex, and the extended ℤ-indexed cochain with
`a_* F` in degree `-1`. Here `a` is the morphism of ringed topoi induced by the
augmentation, and `a_n = a ∘ g_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos C J K u0).ringDirectImage.obj O)
include h_morphism
include h_aug

/-- The ringed site `(Sh(D), O_D)` of the augmentation target. -/
abbrev augmentationRingedSite : RingedSite.{u, v, w} :=
  ofRingSheaf K.toGrothendieck O_D

/-- The morphism of ringed topoi `a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` induced by
the augmentation `u0` and the ring map `aSharp : O_D ⟶ a_* O`. -/
def moduleAugmentationHom :
    ToposHom (totalRingedSite C J O) (augmentationRingedSite K O_D) where
  toTopos := IsAugmentation.totalTopos C J K u0
  structureMap :=
    ((IsAugmentation.totalTopos C J K u0).ringAdjunction.homEquiv O_D O).symm aSharp

/-- The underlying topos morphism of `moduleAugmentationHom` is the augmentation
morphism `IsAugmentation.totalTopos`. -/
theorem moduleAugmentationHom_toTopos :
    (moduleAugmentationHom C J K u0 O O_D aSharp).toTopos =
      IsAugmentation.totalTopos C J K u0 :=
  sorry

variable [(SheafOfModules.restrictScalars.{w}
    (moduleAugmentationHom C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp
      (moduleAugmentationHom C J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (F : SheafOfModules.{w} O)

/-- Continuous-site comparison `f_φ^* F_m ⟶ g_n^* F` from the mate of
`stageInclusionWhisker`. -/
def moduleRestrictDirect_pullbackAux {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap_pullback C J O φ).obj
      ((stageMorphism C J O m).modulePullback.obj F) ⟶
      (Cocontinuous.moduleInverseImage (ofStage C n) O).obj F :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (ringedToposMapDirectStructure C J O φ)).homEquiv
      ((stageMorphism C J O m).modulePullback.obj F)
      ((Cocontinuous.moduleInverseImage (ofStage C n) O).obj F)).symm
    ((moduleInverseImageIsoModulePullback C J O m).inv.app F ≫
      (SheafOfModules.pushforwardNatTrans (𝟙 (componentRingSheaf C J O m))
          (stageInclusionWhisker C φ)).app F ≫
      (SheafOfModules.pushforwardComp (ringedToposMapDirectStructure C J O φ)
          (𝟙 (componentRingSheaf C J O n))).inv.app F)

/-- Restriction `f_φ^* F_m ⟶ F_n` along the simplicial 2-cell. -/
def moduleRestrictDirect_pullback {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePullback.obj
      ((stageMorphism C J O m).modulePullback.obj F) ⟶
      (stageMorphism C J O n).modulePullback.obj F :=
  (ringedToposMap_pullbackIso C J O φ).inv.app
      ((stageMorphism C J O m).modulePullback.obj F) ≫
    moduleRestrictDirect_pullbackAux C J O F φ ≫
    (moduleInverseImageIsoModulePullback C J O n).hom.app F

/-- The comparison `F_m ⟶ f_{φ,*} F_n` adjunct to `moduleRestrictDirect_pullback`. -/
def moduleRestrictDirect {m n : SimplexCategory} (φ : m ⟶ n) :
    (stageMorphism C J O m).modulePullback.obj F ⟶
      (ringedToposMap C J O φ).modulePushforward.obj
        ((stageMorphism C J O n).modulePullback.obj F) :=
  ((ringedToposMap C J O φ).moduleAdjunction.homEquiv
      ((stageMorphism C J O m).modulePullback.obj F)
      ((stageMorphism C J O n).modulePullback.obj F))
    (moduleRestrictDirect_pullback C J O F φ)

/-- Underlying type-valued sheaves identify the composite of module pushforwards along
`f_φ` and `a_m` with module pushforward along `f_φ` then `a_m`. -/
def modulePushforwardCompIso_augmentation_underlying {m n : SimplexCategory}
    (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).modulePushforward ⋙
        ((stageMorphism C J O m).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying O_D ≅
      ((ringedToposMap C J O φ).comp
          ((stageMorphism C J O m).comp
            (moduleAugmentationHom C J K u0 O O_D aSharp))).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying O_D :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ringedToposMap C J O φ).modulePushforward
      (ToposHom.ModulePushforward.forgetIso
        ((stageMorphism C J O m).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ToposHom.ModulePushforward.forgetIso (ringedToposMap C J O φ))
      ((stageMorphism C J O m).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    (ToposHom.ModulePushforward.forgetIso
      ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp)))).symm

/-- Module pushforwards along `f_φ` and `a_m` compose as `(f_φ then a_m)_*`. -/
def modulePushforwardCompIso_augmentation {m n : SimplexCategory} (φ : m ⟶ n) :
    (ringedToposMap C J O φ).modulePushforward ⋙
      ((stageMorphism C J O m).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward ≅
      ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp))).modulePushforward :=
  moduleIsoOfUnderlying
    (modulePushforwardCompIso_augmentation_underlying C J K u0 O O_D aSharp φ)

/-- Inverse-image form of `a_m ∘ f_φ = a_n`, from `a ∘ g_k = a_k` and
`a_m ∘ f_φ = a_n` for the augmentation. -/
def moduleAugmentation_inverseImageIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp))).toTopos.inverseImage ≅
      ((stageMorphism C J O n).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).toTopos.inverseImage :=
  Functor.isoWhiskerRight
      (IsAugmentation.totalTopos_comp_ofStage C J K u0 m)
      (IsAugmentation.faceTopos C J φ).inverseImage ≪≫
    IsAugmentation.stageTopos_comp C J K u0 φ ≪≫
    (IsAugmentation.totalTopos_comp_ofStage C J K u0 n).symm

/-- Underlying type-valued sheaves identify `(a_m ∘ f_φ)_*` with `a_{n,*}`. -/
def moduleAugmentation_2cell_underlying {m n : SimplexCategory} (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp))).modulePushforward ⋙
      Sheaf.InternalModule.ToInternal.underlying O_D ≅
      ((stageMorphism C J O n).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying O_D :=
  ToposHom.ModulePushforward.forgetIso
      ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp))) ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n))
      (MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
        (((ringedToposMap C J O φ).comp
            ((stageMorphism C J O m).comp
              (moduleAugmentationHom C J K u0 O O_D aSharp))).toTopos)
        (((stageMorphism C J O n).comp
            (moduleAugmentationHom C J K u0 O O_D aSharp)).toTopos)
        (moduleAugmentation_inverseImageIso C J K u0 O O_D aSharp φ)) ≪≫
    (ToposHom.ModulePushforward.forgetIso
      ((stageMorphism C J O n).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp))).symm

/-- Direct-image form of `a_m ∘ f_φ = a_n` on modules. -/
def moduleAugmentation_2cell {m n : SimplexCategory} (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp))).modulePushforward ≅
      ((stageMorphism C J O n).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward :=
  moduleIsoOfUnderlying (moduleAugmentation_2cell_underlying C J K u0 O O_D aSharp φ)

/-- The structure map `a_{m,*} F_m ⟶ a_{n,*} F_n` induced by a simplex operator
`φ : m ⟶ n`. -/
def moduleStagePushforward_map {m n : SimplexCategory} (φ : m ⟶ n) :
    ((stageMorphism C J O m).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.obj
      ((stageMorphism C J O m).modulePullback.obj F) ⟶
    ((stageMorphism C J O n).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.obj
      ((stageMorphism C J O n).modulePullback.obj F) :=
  ((stageMorphism C J O m).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.map
      (moduleRestrictDirect C J O F φ) ≫
    (modulePushforwardCompIso_augmentation C J K u0 O O_D aSharp φ).hom.app
      ((stageMorphism C J O n).modulePullback.obj F) ≫
    (moduleAugmentation_2cell C J K u0 O O_D aSharp φ).hom.app
      ((stageMorphism C J O n).modulePullback.obj F)

/-- Identity simplex operators induce identity structure maps of `n ↦ a_{n,*} F_n`. -/
theorem moduleStagePushforward_map_id (n : SimplexCategory) :
    moduleStagePushforward_map C J K u0 O O_D aSharp F (𝟙 n) =
      𝟙 (((stageMorphism C J O n).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.obj
        ((stageMorphism C J O n).modulePullback.obj F)) :=
  sorry

/-- Structure maps of `n ↦ a_{n,*} F_n` are functorial in simplex operators. -/
theorem moduleStagePushforward_map_comp {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    moduleStagePushforward_map C J K u0 O O_D aSharp F (ψ ≫ φ) =
      moduleStagePushforward_map C J K u0 O O_D aSharp F ψ ≫
        moduleStagePushforward_map C J K u0 O O_D aSharp F φ :=
  sorry

/-- The cosimplicial sheaf of `O_D`-modules `n ↦ a_{n,*} F_n`. -/
def modulePushforwardCosimplicial :
    CosimplicialObject (SheafOfModules.{w} O_D) where
  obj n :=
    ((stageMorphism C J O n).comp
        (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.obj
      ((stageMorphism C J O n).modulePullback.obj F)
  map φ := moduleStagePushforward_map C J K u0 O O_D aSharp F φ
  map_id := moduleStagePushforward_map_id C J K u0 O O_D aSharp F
  map_comp := moduleStagePushforward_map_comp C J K u0 O O_D aSharp F

/-- Degree `n` of `modulePushforwardCosimplicial` is the sheaf of modules
`a_{n,*} F_n`. -/
theorem modulePushforwardCosimplicial_obj (n : SimplexCategory) :
    (modulePushforwardCosimplicial C J K u0 O O_D aSharp F).obj n =
      ((stageMorphism C J O n).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.obj
        ((stageMorphism C J O n).modulePullback.obj F) :=
  sorry

/-- The unaugmented cochain `a_{0,*} F_0 ⟶ a_{1,*} F_1 ⟶ ⋯` of `O_D`-modules. -/
abbrev moduleAugmentationCechComplex :
    CochainComplex (SheafOfModules.{w} O_D) ℕ :=
  (alternatingCofaceMapComplex _).obj
    (modulePushforwardCosimplicial C J K u0 O O_D aSharp F)

/-- Degree `n` of `moduleAugmentationCechComplex` is `a_{n,*} F_n`. -/
theorem moduleAugmentationCechComplex_X (n : ℕ) :
    (moduleAugmentationCechComplex C J K u0 O O_D aSharp F).X n =
      (modulePushforwardCosimplicial C J K u0 O O_D aSharp F).obj ⦋n⦌ :=
  sorry

/-- Differentials of `moduleAugmentationCechComplex` are the alternating sums of
coface maps. -/
theorem moduleAugmentationCechComplex_d_eq (n : ℕ) :
    (moduleAugmentationCechComplex C J K u0 O O_D aSharp F).d n (n + 1) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) •
          (modulePushforwardCosimplicial C J K u0 O O_D aSharp F).δ i :=
  sorry

/-- The connecting differential `a_* F ⟶ a_{0,*} F_0` from the `g_0`-unit and the
pushforward composition iso. -/
def moduleAugmentationCechConnect_d₀ :
    ((ChainComplex.single₀ _).obj
        ((moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.obj F)).X 0 ⟶
      (moduleAugmentationCechComplex C J K u0 O O_D aSharp F).X 0 :=
  (moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.map
      ((stageMorphism C J O ⦋0⦌).moduleAdjunction.unit.app F) ≫
    (stageModulePushforwardCompIso C J O
        (moduleAugmentationHom C J K u0 O O_D aSharp) ⦋0⦌).hom.app
      ((stageMorphism C J O ⦋0⦌).modulePullback.obj F)

/-- `moduleAugmentationCechConnect_d₀` is `a_*` of the `g_0`-unit followed by the
identification `a_* g_{0,*} F_0 ≅ a_{0,*} F_0`. -/
theorem moduleAugmentationCechConnect_d₀_eq :
    moduleAugmentationCechConnect_d₀ C J K u0 O O_D aSharp F =
      (moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.map
          ((stageMorphism C J O ⦋0⦌).moduleAdjunction.unit.app F) ≫
        (stageModulePushforwardCompIso C J O
            (moduleAugmentationHom C J K u0 O O_D aSharp) ⦋0⦌).hom.app
          ((stageMorphism C J O ⦋0⦌).modulePullback.obj F) :=
  sorry

/-- The connecting differential annihilates the outgoing differential of
`single₀ (a_* F)`. -/
theorem moduleAugmentationCechConnect_comp_d₀ :
    ((ChainComplex.single₀ _).obj
          ((moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.obj F)).d 1 0 ≫
        moduleAugmentationCechConnect_d₀ C J K u0 O O_D aSharp F = 0 :=
  sorry

/-- The connecting differential annihilates the incoming differential of
`moduleAugmentationCechComplex`. -/
theorem moduleAugmentationCechConnect_d₀_comp :
    moduleAugmentationCechConnect_d₀ C J K u0 O O_D aSharp F ≫
      (moduleAugmentationCechComplex C J K u0 O O_D aSharp F).d 0 1 = 0 :=
  sorry

/-- Connecting data for the ℤ-indexed cochain, with `a_* F` in degree `-1`. -/
def moduleAugmentationCechConnect :
    CochainComplex.ConnectData
      ((ChainComplex.single₀ _).obj
        ((moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.obj F))
      (moduleAugmentationCechComplex C J K u0 O O_D aSharp F) where
  d₀ := moduleAugmentationCechConnect_d₀ C J K u0 O O_D aSharp F
  comp_d₀ := moduleAugmentationCechConnect_comp_d₀ C J K u0 O O_D aSharp F
  d₀_comp := moduleAugmentationCechConnect_d₀_comp C J K u0 O O_D aSharp F

/-- The canonical cochain `0 ⟶ a_* F ⟶ a_{0,*} F_0 ⟶ a_{1,*} F_1 ⟶ ⋯` of
`O_D`-modules. -/
def moduleAugmentationCechCochain :
    CochainComplex (SheafOfModules.{w} O_D) ℤ :=
  (moduleAugmentationCechConnect C J K u0 O O_D aSharp F).cochainComplex

/-- Degree `-1` of `moduleAugmentationCechCochain` is the sheaf of modules `a_* F`. -/
theorem moduleAugmentationCechCochain_X_negOne :
    (moduleAugmentationCechCochain C J K u0 O O_D aSharp F).X (-1) =
      (moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.obj F :=
  sorry

/-- Degree `n ≥ 0` of `moduleAugmentationCechCochain` is `a_{n,*} F_n`. -/
theorem moduleAugmentationCechCochain_X_ofNat (n : ℕ) :
    (moduleAugmentationCechCochain C J K u0 O O_D aSharp F).X n =
      ((stageMorphism C J O ⦋n⦌).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.obj
        ((stageMorphism C J O ⦋n⦌).modulePullback.obj F) :=
  sorry

/-- The differential out of degree `-1` is the comparison `a_* F ⟶ a_{0,*} F_0`. -/
theorem moduleAugmentationCechCochain_d_negOne_zero :
    (moduleAugmentationCechCochain C J K u0 O O_D aSharp F).d (-1) 0 =
      moduleAugmentationCechConnect_d₀ C J K u0 O O_D aSharp F :=
  sorry

/-- The cochain obtained by applying `Hom_{O_D}(G, -)` to
`moduleAugmentationCechCochain`. -/
def homModuleAugmentationCechCochain (G : SheafOfModules.{w} O_D) :
    CochainComplex AddCommGrpCat ℤ :=
  ((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (moduleAugmentationCechCochain C J K u0 O O_D aSharp F)

/-- Degree `n` of `homModuleAugmentationCechCochain` is
`Hom_{O_D}(G, X n)`. -/
theorem homModuleAugmentationCechCochain_X
    (G : SheafOfModules.{w} O_D) (n : ℤ) :
    (homModuleAugmentationCechCochain C J K u0 O O_D aSharp F G).X n =
      (preadditiveCoyoneda.obj (op G)).obj
        ((moduleAugmentationCechCochain C J K u0 O O_D aSharp F).X n) :=
  sorry

end CategoryTheory.SimplicialSites

