module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleResolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Augmented module Čech cochains

Stagewise direct images form a cosimplicial module sheaf and its augmented
alternating-coface complex.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable [UnivLE.{max u v, w}]

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

variable [(SheafOfModules.restrictScalars.{w}
    (IsAugmentation.ringedHom C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp
      (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (F : SheafOfModules.{w} O)

/-- Continuous-site comparison `f_φ^* F_m ⟶ g_n^* F` from the mate of
`stageInclusionWhisker`. -/
private def moduleRestrictDirect_pullbackAux {m n : SimplexCategory} (φ : m ⟶ n) :
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

/-- Inverse-image form of `a_m ∘ f_φ = a_n`, from `a ∘ g_k = a_k` and
`a_m ∘ f_φ = a_n` for the augmentation. -/
private def moduleAugmentation_inverseImageIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp))).toTopos.inverseImage ≅
      ((stageMorphism C J O n).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).toTopos.inverseImage :=
  Functor.isoWhiskerRight
      (IsAugmentation.totalTopos_comp_ofStage C J K u0 m)
      (toposMap C J φ).inverseImage ≪≫
    IsAugmentation.stageTopos_comp C J K u0 φ ≪≫
    (IsAugmentation.totalTopos_comp_ofStage C J K u0 n).symm

/-- Underlying type-valued sheaves identify `(a_m ∘ f_φ)_*` with `a_{n,*}`. -/
private def moduleAugmentation_2cell_underlying {m n : SimplexCategory} (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp))).modulePushforward ⋙
      Sheaf.InternalModule.ToInternal.underlying O_D ≅
      ((stageMorphism C J O n).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying O_D :=
  ToposHom.ModulePushforward.forgetIso
      ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp))) ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying (componentRingSheaf C J O n))
      (MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
        (((ringedToposMap C J O φ).comp
            ((stageMorphism C J O m).comp
              (IsAugmentation.ringedHom C J K u0 O O_D aSharp))).toTopos)
        (((stageMorphism C J O n).comp
            (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).toTopos)
        (moduleAugmentation_inverseImageIso C J K u0 O O_D aSharp φ)) ≪≫
    (ToposHom.ModulePushforward.forgetIso
      ((stageMorphism C J O n).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp))).symm

/-- Direct-image form of `a_m ∘ f_φ = a_n` on modules. -/
private def moduleAugmentation_2cell {m n : SimplexCategory} (φ : m ⟶ n) :
    ((ringedToposMap C J O φ).comp
        ((stageMorphism C J O m).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp))).modulePushforward ≅
      ((stageMorphism C J O n).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward :=
  by
  let e := moduleAugmentation_2cell_underlying C J K u0 O O_D aSharp φ
  have linear :
      (∀ (N : SheafOfModules.{w} (componentRingSheaf C J O n)) U
          (x y : (((ringedToposMap C J O φ).comp
            ((stageMorphism C J O m).comp
              (IsAugmentation.ringedHom C J K u0 O O_D aSharp))).modulePushforward.obj N).val.obj U),
        Sheaf.InternalModule.underlyingApp O_D (e.hom.app N) U (x + y) =
          Sheaf.InternalModule.underlyingApp O_D (e.hom.app N) U x +
            Sheaf.InternalModule.underlyingApp O_D (e.hom.app N) U y) ∧
      (∀ (N : SheafOfModules.{w} (componentRingSheaf C J O n)) U
          (r : O_D.obj.obj U)
          (x : (((ringedToposMap C J O φ).comp
            ((stageMorphism C J O m).comp
              (IsAugmentation.ringedHom C J K u0 O O_D aSharp))).modulePushforward.obj N).val.obj U),
        Sheaf.InternalModule.underlyingApp O_D (e.hom.app N) U (r • x) =
          r • Sheaf.InternalModule.underlyingApp O_D (e.hom.app N) U x) := by
    sorry
  exact Sheaf.InternalModule.functorIsoOfUnderlying O_D e linear.1 linear.2

/-- The structure map `a_{m,*} F_m ⟶ a_{n,*} F_n` induced by a simplex operator
`φ : m ⟶ n`. -/
def moduleStagePushforward_map {m n : SimplexCategory} (φ : m ⟶ n) :
    ((stageMorphism C J O m).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward.obj
      ((stageMorphism C J O m).modulePullback.obj F) ⟶
    ((stageMorphism C J O n).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward.obj
      ((stageMorphism C J O n).modulePullback.obj F) :=
  ((stageMorphism C J O m).comp
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward.map
      (moduleRestrictDirect C J O F φ) ≫
    (ToposHom.modulePushforwardCompIso (ringedToposMap C J O φ)
      ((stageMorphism C J O m).comp (IsAugmentation.ringedHom C J K u0 O O_D aSharp))).hom.app
      ((stageMorphism C J O n).modulePullback.obj F) ≫
    (moduleAugmentation_2cell C J K u0 O O_D aSharp φ).hom.app
      ((stageMorphism C J O n).modulePullback.obj F)

/-- Identity simplex operators induce identity structure maps of `n ↦ a_{n,*} F_n`. -/
theorem moduleStagePushforward_map_id (n : SimplexCategory) :
    moduleStagePushforward_map C J K u0 O O_D aSharp F (𝟙 n) =
      𝟙 (((stageMorphism C J O n).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward.obj
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
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward.obj
      ((stageMorphism C J O n).modulePullback.obj F)
  map φ := moduleStagePushforward_map C J K u0 O O_D aSharp F φ
  map_id := moduleStagePushforward_map_id C J K u0 O O_D aSharp F
  map_comp := moduleStagePushforward_map_comp C J K u0 O O_D aSharp F

/-- Degree `n` of `modulePushforwardCosimplicial` is the sheaf of modules
`a_{n,*} F_n`. -/
theorem modulePushforwardCosimplicial_obj (n : SimplexCategory) :
    (modulePushforwardCosimplicial C J K u0 O O_D aSharp F).obj n =
      ((stageMorphism C J O n).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward.obj
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
        ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePushforward.obj F)).X 0 ⟶
      (moduleAugmentationCechComplex C J K u0 O O_D aSharp F).X 0 :=
  (IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePushforward.map
      ((stageMorphism C J O ⦋0⦌).moduleAdjunction.unit.app F) ≫
    (ToposHom.modulePushforwardCompIso (stageMorphism C J O ⦋0⦌)
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).hom.app
      ((stageMorphism C J O ⦋0⦌).modulePullback.obj F)

/-- `moduleAugmentationCechConnect_d₀` is `a_*` of the `g_0`-unit followed by the
identification `a_* g_{0,*} F_0 ≅ a_{0,*} F_0`. -/
theorem moduleAugmentationCechConnect_d₀_eq :
    moduleAugmentationCechConnect_d₀ C J K u0 O O_D aSharp F =
      (IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePushforward.map
          ((stageMorphism C J O ⦋0⦌).moduleAdjunction.unit.app F) ≫
        (ToposHom.modulePushforwardCompIso (stageMorphism C J O ⦋0⦌)
        (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).hom.app
          ((stageMorphism C J O ⦋0⦌).modulePullback.obj F) :=
  sorry

/-- The connecting differential annihilates the outgoing differential of
`single₀ (a_* F)`. -/
theorem moduleAugmentationCechConnect_comp_d₀ :
    ((ChainComplex.single₀ _).obj
          ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePushforward.obj F)).d 1 0 ≫
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
        ((IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePushforward.obj F))
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
      (IsAugmentation.ringedHom C J K u0 O O_D aSharp).modulePushforward.obj F :=
  sorry

/-- Degree `n ≥ 0` of `moduleAugmentationCechCochain` is `a_{n,*} F_n`. -/
theorem moduleAugmentationCechCochain_X_ofNat (n : ℕ) :
    (moduleAugmentationCechCochain C J K u0 O O_D aSharp F).X n =
      ((stageMorphism C J O ⦋n⦌).comp
          (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).modulePushforward.obj
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

/-- The canonical augmented direct-image cochain is exact in degrees `-1` and `0`. -/
theorem moduleAugmentationCechCochain_exactAt_negOne_zero
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)) :
    (moduleAugmentationCechCochain C J K u0 O O_D aSharp F).ExactAt n :=
  sorry

/-- The augmented direct-image cochain of an injective module is acyclic. -/
theorem moduleAugmentationCechCochain_acyclic_of_injective [Injective F] :
    (moduleAugmentationCechCochain C J K u0 O O_D aSharp F).Acyclic :=
  sorry

/-- The additive Hom image of the augmented direct-image cochain of an injective module is acyclic for every target module. -/
theorem homModuleAugmentationCechCochain_acyclic_of_injective
    [Injective F] (G : SheafOfModules.{w} O_D) :
    (homModuleAugmentationCechCochain C J K u0 O O_D aSharp F G).Acyclic :=
  sorry

end CategoryTheory.SimplicialSites

