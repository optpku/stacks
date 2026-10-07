module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import stacks_project.Chap85.Lemma_85_4_2_Fiberwise
public import stacks_project.Chap85.Lemma_85_11_2_Fiberwise

/-!
# Augmentation Čech cochain of an `O`-module on a fiberwise simplicial site

In Situation 85.3.3 case B, with an augmentation towards a site `D` as in
Remark 85.4.1 and a ring map `O_D ⟶ a_* O`, an `O`-module `M` on the total
Grothendieck construction determines the cosimplicial sheaf of `O_D`-modules
`n ↦ a_{n,*} M_n`, the unaugmented alternating-coface complex, and the extended
ℤ-indexed cochain with `a_* M` in degree `-1`. Here `a` is the morphism of
ringed topoi induced by the augmentation, and `a_n = a ∘ g_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos F J K u0).ringDirectImage.obj O)
include h_fiberwise
include h_aug

/-- The ringed site `(Sh(D), O_D)` of the fiberwise augmentation target. -/
abbrev fiberAugmentationRingedSite : RingedSite.{u, v, w} :=
  ofRingSheaf K.toGrothendieck O_D

/-- The morphism of ringed topoi `a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` induced by
the fiberwise augmentation `u0` and the ring map `aSharp : O_D ⟶ a_* O`. -/
def fiberModuleAugmentationHom :
    ToposHom (fiberTotalRingedSite F J O) (fiberAugmentationRingedSite K O_D) where
  toTopos := IsAugmentation.totalTopos F J K u0
  structureMap :=
    ((IsAugmentation.totalTopos F J K u0).ringAdjunction.homEquiv O_D O).symm aSharp

/-- The underlying topos morphism of `fiberModuleAugmentationHom` is the
augmentation morphism `IsAugmentation.totalTopos`. -/
theorem fiberModuleAugmentationHom_toTopos :
    (fiberModuleAugmentationHom F J K u0 O O_D aSharp).toTopos =
      IsAugmentation.totalTopos F J K u0 :=
  sorry

variable [(SheafOfModules.restrictScalars.{w}
    (fiberModuleAugmentationHom F J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp
      (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (M : SheafOfModules.{w} O)

/-- The `ιNatTrans` 2-cell on underlying type-valued sheaves of `F_m` and `F_n`. -/
def fiberModuleRestrictDirect_underlying {m n : SimplexCategory} (φ : m ⟶ n) :
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck).obj
      ((Sheaf.InternalModule.ToInternal.underlying
          (fiberComponentRingSheaf F J O m)).obj
        ((fiberStageMorphism F J O m).modulePullback.obj M)) ⟶
      ((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M) :=
  (presheafToSheaf ((J (op n)).toGrothendieck) (Type w)).map
      (whiskerLeft (F.map φ.op).toFunctor.op
        ((sheafToPresheaf ((J (op m)).toGrothendieck) (Type w)).map
          (fiberModulePullback_underlyingIso F J O m M).hom)) ≫
    (presheafToSheaf ((J (op n)).toGrothendieck) (Type w)).map
      (whiskerRight (NatTrans.op (ιNatTrans φ.op))
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M).obj) ≫
    (sheafificationAdjunction ((J (op n)).toGrothendieck) (Type w)).counit.app
      (((ι F (op n)).sheafPushforwardContinuous (Type w)
          (J (op n)).toGrothendieck (topology F J)).obj
        ((Sheaf.InternalModule.ToInternal.underlying O).obj M))

/-- Geometric inverse-image comparison `f_φ^{-1} F_m ⟶ restrict F_n` along
`ιNatTrans`. -/
def fiberModuleRestrictDirect_geometric {m n : SimplexCategory} (φ : m ⟶ n) :
    ((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
        (fiberComponentRingSheaf F J O m)).obj
      ((fiberStageMorphism F J O m).modulePullback.obj M) ⟶
      (SheafOfModules.restrictScalars (fiberRingedToposMap F J O φ).structureMap).obj
        ((fiberStageMorphism F J O n).modulePullback.obj M) :=
  Sheaf.InternalModule.homOfUnderlying
    ((fiberRingedToposMap F J O φ).toTopos.ringInverseImage.obj
      (fiberComponentRingSheaf F J O m))
    (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImageForgetIso
        (fiberComponentRingSheaf F J O m)).hom.app
        ((fiberStageMorphism F J O m).modulePullback.obj M) ≫
      fiberModuleRestrictDirect_underlying F J O M φ ≫
      (fiberModulePullback_underlyingIso F J O n M).inv ≫
      (fiberRingedToposMap_restrictScalars_forgetIso F J O φ
          ((fiberStageMorphism F J O n).modulePullback.obj M)).inv)
    sorry sorry

/-- Restriction `f_φ^* F_m ⟶ F_n` along the simplicial 2-cell in case B. -/
def fiberModuleRestrictDirect_pullback {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberRingedToposMap F J O φ).modulePullback.obj
      ((fiberStageMorphism F J O m).modulePullback.obj M) ⟶
      (fiberStageMorphism F J O n).modulePullback.obj M :=
  (ToposHom.ModulePullback.scalarHomEquiv (fiberRingedToposMap F J O φ)
      (((fiberRingedToposMap F J O φ).toTopos.moduleInverseImage
          (fiberComponentRingSheaf F J O m)).obj
        ((fiberStageMorphism F J O m).modulePullback.obj M))
      ((fiberStageMorphism F J O n).modulePullback.obj M)).symm
    (fiberModuleRestrictDirect_geometric F J O M φ)

/-- The comparison `F_m ⟶ f_{φ,*} F_n` adjunct to
`fiberModuleRestrictDirect_pullback`. -/
def fiberModuleRestrictDirect {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberStageMorphism F J O m).modulePullback.obj M ⟶
      (fiberRingedToposMap F J O φ).modulePushforward.obj
        ((fiberStageMorphism F J O n).modulePullback.obj M) :=
  ((fiberRingedToposMap F J O φ).moduleAdjunction.homEquiv
      ((fiberStageMorphism F J O m).modulePullback.obj M)
      ((fiberStageMorphism F J O n).modulePullback.obj M))
    (fiberModuleRestrictDirect_pullback F J O M φ)

/-- Underlying type-valued sheaves identify the composite of module pushforwards along
`f_φ` and `a_m` with module pushforward along `f_φ` then `a_m` in case B. -/
def fiberModulePushforwardCompIso_augmentation_underlying {m n : SimplexCategory}
    (φ : m ⟶ n) :
    ((fiberRingedToposMap F J O φ).modulePushforward ⋙
        ((fiberStageMorphism F J O m).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward) ⋙
      Sheaf.InternalModule.ToInternal.underlying O_D ≅
      ((fiberRingedToposMap F J O φ).comp
          ((fiberStageMorphism F J O m).comp
            (fiberModuleAugmentationHom F J K u0 O O_D aSharp))).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying O_D :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fiberRingedToposMap F J O φ).modulePushforward
      (ToposHom.ModulePushforward.forgetIso
        ((fiberStageMorphism F J O m).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ToposHom.ModulePushforward.forgetIso (fiberRingedToposMap F J O φ))
      ((fiberStageMorphism F J O m).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    (ToposHom.ModulePushforward.forgetIso
      ((fiberRingedToposMap F J O φ).comp
        ((fiberStageMorphism F J O m).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp)))).symm

/-- Module pushforwards along `f_φ` and `a_m` compose as `(f_φ then a_m)_*` in
case B. -/
def fiberModulePushforwardCompIso_augmentation {m n : SimplexCategory} (φ : m ⟶ n) :
    (fiberRingedToposMap F J O φ).modulePushforward ⋙
      ((fiberStageMorphism F J O m).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward ≅
      ((fiberRingedToposMap F J O φ).comp
        ((fiberStageMorphism F J O m).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp))).modulePushforward :=
  moduleIsoOfUnderlying
    (fiberModulePushforwardCompIso_augmentation_underlying F J K u0 O O_D aSharp φ)

/-- Inverse-image form of `a_m ∘ f_φ = a_n` in case B, from `a ∘ g_k = a_k` and
`a_m ∘ f_φ = a_n` for the fiberwise augmentation. -/
def fiberModuleAugmentation_inverseImageIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((fiberRingedToposMap F J O φ).comp
        ((fiberStageMorphism F J O m).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp))).toTopos.inverseImage ≅
      ((fiberStageMorphism F J O n).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).toTopos.inverseImage :=
  Functor.isoWhiskerRight
      (IsAugmentation.totalTopos_comp_fiberMorphism F J K u0 m)
      (IsAugmentation.faceTopos F J φ).inverseImage ≪≫
    IsAugmentation.stageTopos_comp F J K u0 φ ≪≫
    (IsAugmentation.totalTopos_comp_fiberMorphism F J K u0 n).symm

/-- Underlying type-valued sheaves identify `(a_m ∘ f_φ)_*` with `a_{n,*}` in
case B. -/
def fiberModuleAugmentation_2cell_underlying {m n : SimplexCategory} (φ : m ⟶ n) :
    ((fiberRingedToposMap F J O φ).comp
        ((fiberStageMorphism F J O m).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp))).modulePushforward ⋙
      Sheaf.InternalModule.ToInternal.underlying O_D ≅
      ((fiberStageMorphism F J O n).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward ⋙
        Sheaf.InternalModule.ToInternal.underlying O_D :=
  ToposHom.ModulePushforward.forgetIso
      ((fiberRingedToposMap F J O φ).comp
        ((fiberStageMorphism F J O m).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp))) ≪≫
    Functor.isoWhiskerLeft
      (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n))
      (MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
        (((fiberRingedToposMap F J O φ).comp
            ((fiberStageMorphism F J O m).comp
              (fiberModuleAugmentationHom F J K u0 O O_D aSharp))).toTopos)
        (((fiberStageMorphism F J O n).comp
            (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).toTopos)
        (fiberModuleAugmentation_inverseImageIso F J K u0 O O_D aSharp φ)) ≪≫
    (ToposHom.ModulePushforward.forgetIso
      ((fiberStageMorphism F J O n).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp))).symm

/-- Direct-image form of `a_m ∘ f_φ = a_n` on modules in case B. -/
def fiberModuleAugmentation_2cell {m n : SimplexCategory} (φ : m ⟶ n) :
    ((fiberRingedToposMap F J O φ).comp
        ((fiberStageMorphism F J O m).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp))).modulePushforward ≅
      ((fiberStageMorphism F J O n).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward :=
  moduleIsoOfUnderlying
    (fiberModuleAugmentation_2cell_underlying F J K u0 O O_D aSharp φ)

/-- The structure map `a_{m,*} M_m ⟶ a_{n,*} M_n` induced by a fiberwise simplex
operator `φ : m ⟶ n`. -/
def fiberModuleStagePushforward_map {m n : SimplexCategory} (φ : m ⟶ n) :
    ((fiberStageMorphism F J O m).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward.obj
      ((fiberStageMorphism F J O m).modulePullback.obj M) ⟶
    ((fiberStageMorphism F J O n).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward.obj
      ((fiberStageMorphism F J O n).modulePullback.obj M) :=
  ((fiberStageMorphism F J O m).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward.map
      (fiberModuleRestrictDirect F J O M φ) ≫
    (fiberModulePushforwardCompIso_augmentation F J K u0 O O_D aSharp φ).hom.app
      ((fiberStageMorphism F J O n).modulePullback.obj M) ≫
    (fiberModuleAugmentation_2cell F J K u0 O O_D aSharp φ).hom.app
      ((fiberStageMorphism F J O n).modulePullback.obj M)

/-- Identity simplex operators induce identity structure maps in case B. -/
theorem fiberModuleStagePushforward_map_id (n : SimplexCategory) :
    fiberModuleStagePushforward_map F J K u0 O O_D aSharp M (𝟙 n) =
      𝟙 (((fiberStageMorphism F J O n).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward.obj
        ((fiberStageMorphism F J O n).modulePullback.obj M)) :=
  sorry

/-- Structure maps of `n ↦ a_{n,*} M_n` are functorial in fiberwise simplex
operators. -/
theorem fiberModuleStagePushforward_map_comp {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    fiberModuleStagePushforward_map F J K u0 O O_D aSharp M (ψ ≫ φ) =
      fiberModuleStagePushforward_map F J K u0 O O_D aSharp M ψ ≫
        fiberModuleStagePushforward_map F J K u0 O O_D aSharp M φ :=
  sorry

/-- The cosimplicial sheaf of `O_D`-modules `n ↦ a_{n,*} M_n` in case B. -/
def fiberModulePushforwardCosimplicial :
    CosimplicialObject (SheafOfModules.{w} O_D) where
  obj n :=
    ((fiberStageMorphism F J O n).comp
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward.obj
      ((fiberStageMorphism F J O n).modulePullback.obj M)
  map φ := fiberModuleStagePushforward_map F J K u0 O O_D aSharp M φ
  map_id := fiberModuleStagePushforward_map_id F J K u0 O O_D aSharp M
  map_comp := fiberModuleStagePushforward_map_comp F J K u0 O O_D aSharp M

/-- Degree `n` of `fiberModulePushforwardCosimplicial` is `a_{n,*} M_n`. -/
theorem fiberModulePushforwardCosimplicial_obj (n : SimplexCategory) :
    (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M).obj n =
      ((fiberStageMorphism F J O n).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward.obj
        ((fiberStageMorphism F J O n).modulePullback.obj M) :=
  sorry

/-- The unaugmented cochain `a_{0,*} M_0 ⟶ a_{1,*} M_1 ⟶ ⋯` of `O_D`-modules in
case B. -/
abbrev fiberModuleAugmentationCechComplex :
    CochainComplex (SheafOfModules.{w} O_D) ℕ :=
  (alternatingCofaceMapComplex _).obj
    (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M)

/-- Degree `n` of `fiberModuleAugmentationCechComplex` is `a_{n,*} M_n`. -/
theorem fiberModuleAugmentationCechComplex_X (n : ℕ) :
    (fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp M).X n =
      (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M).obj ⦋n⦌ :=
  sorry

/-- Differentials of `fiberModuleAugmentationCechComplex` are the alternating
sums of coface maps. -/
theorem fiberModuleAugmentationCechComplex_d_eq (n : ℕ) :
    (fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp M).d n (n + 1) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) •
          (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M).δ i :=
  sorry

/-- The connecting differential `a_* M ⟶ a_{0,*} M_0` in case B. -/
def fiberModuleAugmentationCechConnect_d₀ :
    ((ChainComplex.single₀ _).obj
        ((fiberModuleAugmentationHom F J K u0 O O_D aSharp).modulePushforward.obj M)).X 0 ⟶
      (fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp M).X 0 :=
  (fiberModuleAugmentationHom F J K u0 O O_D aSharp).modulePushforward.map
      ((fiberStageMorphism F J O ⦋0⦌).moduleAdjunction.unit.app M) ≫
    (fiberStageModulePushforwardCompIso F J O
        (fiberModuleAugmentationHom F J K u0 O O_D aSharp) ⦋0⦌).hom.app
      ((fiberStageMorphism F J O ⦋0⦌).modulePullback.obj M)

/-- `fiberModuleAugmentationCechConnect_d₀` is `a_*` of the `g_0`-unit followed by
the identification `a_* g_{0,*} M_0 ≅ a_{0,*} M_0`. -/
theorem fiberModuleAugmentationCechConnect_d₀_eq :
    fiberModuleAugmentationCechConnect_d₀ F J K u0 O O_D aSharp M =
      (fiberModuleAugmentationHom F J K u0 O O_D aSharp).modulePushforward.map
          ((fiberStageMorphism F J O ⦋0⦌).moduleAdjunction.unit.app M) ≫
        (fiberStageModulePushforwardCompIso F J O
            (fiberModuleAugmentationHom F J K u0 O O_D aSharp) ⦋0⦌).hom.app
          ((fiberStageMorphism F J O ⦋0⦌).modulePullback.obj M) :=
  sorry

/-- The connecting differential annihilates the outgoing differential of
`single₀ (a_* M)`. -/
theorem fiberModuleAugmentationCechConnect_comp_d₀ :
    ((ChainComplex.single₀ _).obj
          ((fiberModuleAugmentationHom F J K u0 O O_D aSharp).modulePushforward.obj M)).d 1 0 ≫
        fiberModuleAugmentationCechConnect_d₀ F J K u0 O O_D aSharp M = 0 :=
  sorry

/-- The connecting differential annihilates the incoming differential of
`fiberModuleAugmentationCechComplex`. -/
theorem fiberModuleAugmentationCechConnect_d₀_comp :
    fiberModuleAugmentationCechConnect_d₀ F J K u0 O O_D aSharp M ≫
      (fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp M).d 0 1 = 0 :=
  sorry

/-- Connecting data for the ℤ-indexed cochain in case B, with `a_* M` in degree
`-1`. -/
def fiberModuleAugmentationCechConnect :
    CochainComplex.ConnectData
      ((ChainComplex.single₀ _).obj
        ((fiberModuleAugmentationHom F J K u0 O O_D aSharp).modulePushforward.obj M))
      (fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp M) where
  d₀ := fiberModuleAugmentationCechConnect_d₀ F J K u0 O O_D aSharp M
  comp_d₀ := fiberModuleAugmentationCechConnect_comp_d₀ F J K u0 O O_D aSharp M
  d₀_comp := fiberModuleAugmentationCechConnect_d₀_comp F J K u0 O O_D aSharp M

/-- The canonical cochain `0 ⟶ a_* M ⟶ a_{0,*} M_0 ⟶ a_{1,*} M_1 ⟶ ⋯` of
`O_D`-modules in case B. -/
def fiberModuleAugmentationCechCochain :
    CochainComplex (SheafOfModules.{w} O_D) ℤ :=
  (fiberModuleAugmentationCechConnect F J K u0 O O_D aSharp M).cochainComplex

/-- Degree `-1` of `fiberModuleAugmentationCechCochain` is `a_* M`. -/
theorem fiberModuleAugmentationCechCochain_X_negOne :
    (fiberModuleAugmentationCechCochain F J K u0 O O_D aSharp M).X (-1) =
      (fiberModuleAugmentationHom F J K u0 O O_D aSharp).modulePushforward.obj M :=
  sorry

/-- Degree `n ≥ 0` of `fiberModuleAugmentationCechCochain` is `a_{n,*} M_n`. -/
theorem fiberModuleAugmentationCechCochain_X_ofNat (n : ℕ) :
    (fiberModuleAugmentationCechCochain F J K u0 O O_D aSharp M).X n =
      ((fiberStageMorphism F J O ⦋n⦌).comp
          (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).modulePushforward.obj
        ((fiberStageMorphism F J O ⦋n⦌).modulePullback.obj M) :=
  sorry

/-- The differential out of degree `-1` is the comparison `a_* M ⟶ a_{0,*} M_0`. -/
theorem fiberModuleAugmentationCechCochain_d_negOne_zero :
    (fiberModuleAugmentationCechCochain F J K u0 O O_D aSharp M).d (-1) 0 =
      fiberModuleAugmentationCechConnect_d₀ F J K u0 O O_D aSharp M :=
  sorry

/-- The cochain obtained by applying `Hom_{O_D}(G, -)` to
`fiberModuleAugmentationCechCochain`. -/
def fiberHomModuleAugmentationCechCochain
    (G : SheafOfModules.{w} O_D) :
    CochainComplex AddCommGrpCat ℤ :=
  ((preadditiveCoyoneda.obj (op G)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (fiberModuleAugmentationCechCochain F J K u0 O O_D aSharp M)

/-- Degree `n` of `fiberHomModuleAugmentationCechCochain` is
`Hom_{O_D}(G, X n)`. -/
theorem fiberHomModuleAugmentationCechCochain_X
    (G : SheafOfModules.{w} O_D) (n : ℤ) :
    (fiberHomModuleAugmentationCechCochain F J K u0 O O_D aSharp M G).X n =
      (preadditiveCoyoneda.obj (op G)).obj
        ((fiberModuleAugmentationCechCochain F J K u0 O O_D aSharp M).X n) :=
  sorry

end CategoryTheory.Grothendieck
