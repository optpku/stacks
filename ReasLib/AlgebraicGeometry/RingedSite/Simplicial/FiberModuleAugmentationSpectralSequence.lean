/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.EnoughInjectives
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberModuleCech
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment

/-!
# Čech–injective double complex of a fiberwise augmentation of ringed sites

For an augmented simplicial site with a ring map `O_D ⟶ a_* O`, a cochain complex `I` of
`O`-modules on the total fiberwise site determines the double complex
`A^{p,q} = a_{p,*} I^q_p`. The associated first-page and abutment functors on
`DerivedCategory.Plus` recover `R^q a_{p,*} K_p` and `R^n a_* K` as sheaves of
`O_D`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory RingedSite ZeroObject
open scoped HomologicalComplex₂ Simplicial
open FilteredComplex.SpectralSequence.Realization

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
variable [(SheafOfModules.restrictScalars.{w}
    (IsAugmentation.ringedHom F J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp
      (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
include h_fiberwise
include h_aug

/-- Canonical derived-category structure on `O`-modules on the total fiberwise site. -/
instance fiberTotalModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O) :=
  HasDerivedCategory.standard (SheafOfModules.{w} O)

/-- Canonical derived-category structure on `O_D`-modules on the fiberwise augmentation target. -/
instance fiberAugmentationTargetModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O_D) :=
  HasDerivedCategory.standard (SheafOfModules.{w} O_D)

/-- The component of a morphism of `O`-modules under `n ↦ a_{n,*} (-)_n`. -/
def fiberModulePushforwardCosimplicialMap {M N : SheafOfModules.{w} O} (α : M ⟶ N)
    (n : SimplexCategory) :
    (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M).obj n ⟶
      (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp N).obj n :=
  ((fiberStageMorphism F J O n).comp
      (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePushforward.map
    ((fiberStageMorphism F J O n).modulePullback.map α)

/-- Naturality of `fiberModulePushforwardCosimplicialMap` in the simplicial degree. -/
theorem fiberModulePushforwardCosimplicialMap_naturality {M N : SheafOfModules.{w} O}
    (α : M ⟶ N) {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M).map φ ≫
        fiberModulePushforwardCosimplicialMap F J K u0 O O_D aSharp α m =
      fiberModulePushforwardCosimplicialMap F J K u0 O O_D aSharp α n ≫
        (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp N).map φ :=
  sorry

/-- The natural transformation `n ↦ a_{n,*} M_n ⟶ a_{n,*} N_n` induced by `α`. -/
def fiberModulePushforwardCosimplicialNatTrans {M N : SheafOfModules.{w} O} (α : M ⟶ N) :
    fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M ⟶
      fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp N where
  app n := fiberModulePushforwardCosimplicialMap F J K u0 O O_D aSharp α n
  naturality _ _ φ :=
    fiberModulePushforwardCosimplicialMap_naturality F J K u0 O O_D aSharp α φ

/-- Identity morphisms act as the identity on `fiberModulePushforwardCosimplicial`. -/
theorem fiberModulePushforwardCosimplicialNatTrans_id (M : SheafOfModules.{w} O) :
    fiberModulePushforwardCosimplicialNatTrans F J K u0 O O_D aSharp (𝟙 M) =
      𝟙 (fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M) :=
  sorry

/-- `fiberModulePushforwardCosimplicialNatTrans` preserves composition. -/
theorem fiberModulePushforwardCosimplicialNatTrans_comp {M N P : SheafOfModules.{w} O}
    (α : M ⟶ N) (β : N ⟶ P) :
    fiberModulePushforwardCosimplicialNatTrans F J K u0 O O_D aSharp (α ≫ β) =
      fiberModulePushforwardCosimplicialNatTrans F J K u0 O O_D aSharp α ≫
        fiberModulePushforwardCosimplicialNatTrans F J K u0 O O_D aSharp β :=
  sorry

/-- Functoriality of `n ↦ a_{n,*} M_n` in the `O`-module `M`. -/
def fiberModulePushforwardCosimplicialFunctor :
    SheafOfModules.{w} O ⥤ CosimplicialObject (SheafOfModules.{w} O_D) where
  obj M := fiberModulePushforwardCosimplicial F J K u0 O O_D aSharp M
  map α := fiberModulePushforwardCosimplicialNatTrans F J K u0 O O_D aSharp α
  map_id := fiberModulePushforwardCosimplicialNatTrans_id F J K u0 O O_D aSharp
  map_comp := fiberModulePushforwardCosimplicialNatTrans_comp F J K u0 O O_D aSharp

/-- The unaugmented Čech cochain functor `M ↦ (a_{0,*} M_0 → a_{1,*} M_1 → ⋯)`. -/
def fiberModuleAugmentationCechComplexFunctor :
    SheafOfModules.{w} O ⥤ CochainComplex (SheafOfModules.{w} O_D) ℕ :=
  fiberModulePushforwardCosimplicialFunctor F J K u0 O O_D aSharp ⋙
    alternatingCofaceMapComplex _

/-- Evaluation of `fiberModuleAugmentationCechComplexFunctor` recovers the unaugmented Čech cochain complex. -/
theorem fiberModuleAugmentationCechComplexFunctor_obj (M : SheafOfModules.{w} O) :
    (fiberModuleAugmentationCechComplexFunctor F J K u0 O O_D aSharp).obj M =
      fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp M :=
  sorry

/-- The fiberwise Čech cochain functor of a module augmentation preserves zero morphisms. -/
instance fiberModuleAugmentationCechComplexFunctor_preservesZeroMorphisms :
    (fiberModuleAugmentationCechComplexFunctor F J K u0 O O_D aSharp).PreservesZeroMorphisms :=
  sorry

/-- The fiberwise Čech cochain functor of a module augmentation is additive. -/
instance fiberModuleAugmentationCechComplexFunctor_additive :
    (fiberModuleAugmentationCechComplexFunctor F J K u0 O O_D aSharp).Additive :=
  sorry

/-- The ℕ-indexed cochain of vertical complexes `p ↦ (q ↦ a_{p,*} I^q_p)`. -/
def fiberModuleAugmentationColumnsFunctor :
    CochainComplex (SheafOfModules.{w} O) ℤ ⥤
      CochainComplex (CochainComplex (SheafOfModules.{w} O_D) ℤ) ℕ :=
  (fiberModuleAugmentationCechComplexFunctor F J K u0 O O_D aSharp).mapHomologicalComplex
      (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℕ)

/-- The fiberwise Čech–injective double complex functor. -/
def fiberModuleAugmentationBicomplexFunctor :
    CochainComplex (SheafOfModules.{w} O) ℤ ⥤
      HomologicalComplex₂ (SheafOfModules.{w} O_D) (up ℤ) (up ℤ) :=
  fiberModuleAugmentationColumnsFunctor F J K u0 O O_D aSharp ⋙
    HomologicalComplex₂.CoaugmentedResolution.bicomplexFunctor

/-- The double complex `A^{p,q} = a_{p,*} I^q_p`. -/
def fiberModuleAugmentationBicomplex
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    HomologicalComplex₂ (SheafOfModules.{w} O_D) (up ℤ) (up ℤ) :=
  (fiberModuleAugmentationBicomplexFunctor F J K u0 O O_D aSharp).obj I

/-- Nonnegative columns of `fiberModuleAugmentationBicomplex` recover stagewise pushforwards of `I`. -/
theorem fiberModuleAugmentationBicomplex_X_ofNat
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) (p : ℕ) (q : ℤ) :
    ((fiberModuleAugmentationBicomplex F J K u0 O O_D aSharp I).X p).X q =
      ((fiberStageMorphism F J O ⦋p⦌).comp
          (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePushforward.obj
        ((fiberStageMorphism F J O ⦋p⦌).modulePullback.obj (I.X q)) :=
  sorry

/-- Negative Čech columns of `fiberModuleAugmentationBicomplex` vanish. -/
theorem fiberModuleAugmentationBicomplex_isZero_of_neg
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) {p : ℤ} (hp : p < 0) :
    IsZero ((fiberModuleAugmentationBicomplex F J K u0 O O_D aSharp I).X p) :=
  sorry

/-- The coaugmentation source `a_* I^•` as a cochain complex of `O_D`-modules. -/
def fiberModuleAugmentationTotalComplex
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    CochainComplex (SheafOfModules.{w} O_D) ℤ :=
  (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePushforward
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePushforward
      (ToposHom.modulePushforward_additive
        (IsAugmentation.ringedHom F J K u0 O O_D aSharp))) (up ℤ)).obj I

/-- The coaugmentation `a_* I^• ⟶` the zeroth column of the fiberwise Čech bicomplex. -/
def fiberModuleAugmentationCoaugmentation
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    fiberModuleAugmentationTotalComplex F J K u0 O O_D aSharp I ⟶
      ((fiberModuleAugmentationColumnsFunctor F J K u0 O O_D aSharp).obj I).X 0 where
  f q := fiberModuleAugmentationCechConnect_d₀ F J K u0 O O_D aSharp (I.X q)
  comm' := sorry

/-- The coaugmentation is killed by the first Čech differential. -/
theorem fiberModuleAugmentationCoaugmentation_comp_d
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    fiberModuleAugmentationCoaugmentation F J K u0 O O_D aSharp I ≫
      ((fiberModuleAugmentationColumnsFunctor F J K u0 O O_D aSharp).obj I).d 0 1 = 0 :=
  sorry

/-- Degree-`n` functor sending an `O`-module on the total fiberwise site to `a_{n,*} M_n`. -/
def fiberModuleAugmentationStageGamma (n : ℕ) :
    SheafOfModules.{w} O ⥤ SheafOfModules.{w} O_D :=
  (fiberStageMorphism F J O ⦋n⦌).modulePullback ⋙
    ((fiberStageMorphism F J O ⦋n⦌).comp
      (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePushforward

/-- Stagewise fiberwise module-augmentation pushforward recovers `a_{n,*} M_n`. -/
theorem fiberModuleAugmentationStageGamma_obj (n : ℕ) (M : SheafOfModules.{w} O) :
    (fiberModuleAugmentationStageGamma F J K u0 O O_D aSharp n).obj M =
      ((fiberStageMorphism F J O ⦋n⦌).comp
          (IsAugmentation.ringedHom F J K u0 O O_D aSharp)).modulePushforward.obj
        ((fiberStageMorphism F J O ⦋n⦌).modulePullback.obj M) :=
  sorry

/-- Stagewise fiberwise module-augmentation pushforward is additive. -/
instance fiberModuleAugmentationStageGamma_additive (n : ℕ) :
    (fiberModuleAugmentationStageGamma F J K u0 O O_D aSharp n).Additive :=
  sorry

/-- Naturality of the fiberwise Čech differential in the `O`-module. -/
theorem fiberModuleAugmentationStageGamma_d_naturality (n : ℕ)
    {M N : SheafOfModules.{w} O} (α : M ⟶ N) :
    (fiberModuleAugmentationStageGamma F J K u0 O O_D aSharp n).map α ≫
        (fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp N).d n (n + 1) =
      (fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp M).d n (n + 1) ≫
        (fiberModuleAugmentationStageGamma F J K u0 O O_D aSharp (n + 1)).map α :=
  sorry

/-- The Čech differential as a natural transformation of fiberwise stagewise pushforwards. -/
def fiberModuleAugmentationStageGamma_d (n : ℕ) :
    fiberModuleAugmentationStageGamma F J K u0 O O_D aSharp n ⟶
      fiberModuleAugmentationStageGamma F J K u0 O O_D aSharp (n + 1) where
  app M := (fiberModuleAugmentationCechComplex F J K u0 O O_D aSharp M).d n (n + 1)
  naturality _ _ α :=
    fiberModuleAugmentationStageGamma_d_naturality F J K u0 O O_D aSharp n α

/-- The functor on bounded-below homotopy categories induced by augmentation direct image. -/
def fiberModuleAugmentationPushforwardToBoundedBelowDerived :
    HomotopyCategory.Plus (SheafOfModules.{w} O) ⥤
      DerivedCategory.Plus (SheafOfModules.{w} O_D) :=
  @Functor.toBoundedBelowDerived _ _ _ _ _ _ _
    (IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePushforward
    (ToposHom.modulePushforward_additive
      (IsAugmentation.ringedHom F J K u0 O O_D aSharp))

/-- The bounded-below right derived direct image of modules along the augmentation. -/
def fiberModuleAugmentationDerivedPushforward :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤
      DerivedCategory.Plus (SheafOfModules.{w} O_D) :=
  @Functor.RightDerived.Bounded.functor _ _ _ _ _ _ _ _
    (IsAugmentation.ringedHom F J K u0 O O_D aSharp).modulePushforward
    (ToposHom.modulePushforward_additive
      (IsAugmentation.ringedHom F J K u0 O O_D aSharp)) inferInstance

/-- Nonnegative first-page target: `R^q` of `a_{n,*} ((-)_n)`. -/
def fiberModuleAugmentationPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ SheafOfModules.{w} O_D :=
  Functor.RightDerived.Bounded.functor
      (fiberModuleAugmentationStageGamma F J K u0 O O_D aSharp n) ⋙
    DerivedCategory.Plus.homologyFunctor (SheafOfModules.{w} O_D) q

/-- The Čech differential on nonnegative first-page functors. -/
def fiberModuleAugmentationPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    fiberModuleAugmentationPageOneFunctorNonneg F J K u0 O O_D aSharp n q ⟶
      fiberModuleAugmentationPageOneFunctorNonneg F J K u0 O O_D aSharp (n + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map
      (fiberModuleAugmentationStageGamma_d F J K u0 O O_D aSharp n))
    (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{w} O_D) q)

/-- First-page target `K ↦ R^q a_{p,*} K_p`, vanishing for `p < 0`. -/
def fiberModuleAugmentationPageOneFunctor (p q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ SheafOfModules.{w} O_D :=
  if 0 ≤ p then
    fiberModuleAugmentationPageOneFunctorNonneg F J K u0 O O_D aSharp p.toNat q
  else
    (Functor.const (DerivedCategory.Plus (SheafOfModules.{w} O))).obj
      (0 : SheafOfModules.{w} O_D)

/-- Nonnegative bidegrees of `fiberModuleAugmentationPageOneFunctor` recover the nonnegative functor. -/
theorem fiberModuleAugmentationPageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q =
      fiberModuleAugmentationPageOneFunctorNonneg F J K u0 O O_D aSharp p.toNat q :=
  sorry

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def fiberModuleAugmentationPageOneDifferential (p q : ℤ) :
    fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q ⟶
      fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (if_pos hp) ≫
      fiberModuleAugmentationPageOneDifferentialNonneg F J K u0 O O_D aSharp p.toNat q ≫
      eqToHom
        (congrArg (fiberModuleAugmentationPageOneFunctorNonneg F J K u0 O O_D aSharp · q)
          (Int.toNat_add_nat hp 1)).symm ≫
      eqToHom (if_pos (Int.add_nonneg hp zero_le_one)).symm
  else
    (0 : fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q ⟶
      fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp (p + 1) q)

/-- First-page sheaves in negative Čech degree vanish. -/
theorem fiberModuleAugmentationPageOneFunctor_neg
    (X : DerivedCategory.Plus (SheafOfModules.{w} O)) {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).obj X) :=
  sorry

/-- Abutment functor `K ↦ R^n a_* K`. -/
def fiberModuleAugmentationAbutmentFunctor (n : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ SheafOfModules.{w} O_D :=
  fiberModuleAugmentationDerivedPushforward F J K u0 O O_D aSharp ⋙
    DerivedCategory.Plus.homologyFunctor (SheafOfModules.{w} O_D) n

/-- Evaluation of `fiberModuleAugmentationAbutmentFunctor` is cohomology of `R a_*`. -/
theorem fiberModuleAugmentationAbutmentFunctor_obj (n : ℤ)
    (X : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    (fiberModuleAugmentationAbutmentFunctor F J K u0 O O_D aSharp n).obj X =
      (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{w} O_D) n).obj
        ((fiberModuleAugmentationDerivedPushforward F J K u0 O O_D aSharp).obj X) :=
  sorry

/-- For a bounded-below complex of injectives representing `K`, vertical homology of
`fiberModuleAugmentationBicomplex` recovers the first-page target. -/
theorem fiberModuleAugmentationPageOne_isomorphic_of_injectiveRepresentative
    (I : CochainComplex (SheafOfModules.{w} O) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)]
    (X : DerivedCategory.Plus (SheafOfModules.{w} O))
    (hX : Nonempty (DerivedCategory.Plus.ι.obj X ≅ DerivedCategory.Q.obj I))
    (p q : ℤ) :
    IsIsomorphic
      (HomologicalComplex₂.First.PageOne.entry
        (fiberModuleAugmentationBicomplex F J K u0 O O_D aSharp I) p q)
      ((fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).obj X) :=
  sorry

/-- The coaugmentation-to-total comparison is a quasi-isomorphism when every term of `I`
is injective. -/
theorem fiberModuleAugmentationToTotal_quasiIso
    [HasCountableCoproducts (SheafOfModules.{w} O_D)]
    [CountableAB4 (SheafOfModules.{w} O_D)]
    (I : CochainComplex (SheafOfModules.{w} O) ℤ)
    [∀ n, Injective (I.X n)] :
    QuasiIso
      (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map
        ((fiberModuleAugmentationColumnsFunctor F J K u0 O O_D aSharp).obj I)
        (fiberModuleAugmentationCoaugmentation F J K u0 O O_D aSharp I)
        (fiberModuleAugmentationCoaugmentation_comp_d F J K u0 O O_D aSharp I)) :=
  sorry

/-- Every bounded-below derived module on an augmented simplicial site has a
convergent spectral sequence of target modules with derived stage direct images
on the first page and the derived Čech differential. -/
theorem exists_fiberModuleAugmentationSpectralSequence
    (X : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    ∃ (S : WithAbutment
        (fun n ↦ fiberModuleAugmentationAbutmentFunctor F J K u0 O O_D aSharp n) X)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).obj X),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫
            (fiberModuleAugmentationPageOneDifferential F J K u0 O O_D aSharp p q).app X =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- The augmentation spectral sequences can be chosen simultaneously for all
bounded-below derived modules, with natural first-page comparisons and maps
preserving identities and composition on spectral sequences. -/
theorem fiberModuleAugmentationSpectralSequence_functorial :
    ∃ (S : ∀ X : DerivedCategory.Plus (SheafOfModules.{w} O),
        WithAbutment (fun n ↦ fiberModuleAugmentationAbutmentFunctor F J K u0 O O_D aSharp n) X)
      (pageOneIso : ∀ (X : DerivedCategory.Plus (SheafOfModules.{w} O)) (p q : ℤ),
        ((S X).sequence.page 1).X (p, q) ≅
          (fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).obj X)
      (m : ∀ {X Y : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : X ⟶ Y),
        WithAbutment.Map (fun n ↦ fiberModuleAugmentationAbutmentFunctor F J K u0 O O_D aSharp n) f (S X) (S Y)),
      (∀ (X : DerivedCategory.Plus (SheafOfModules.{w} O)) (p q : ℤ),
        (pageOneIso X p q).hom ≫
            (fiberModuleAugmentationPageOneDifferential F J K u0 O O_D aSharp p q).app X =
          ((S X).sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso X (p + 1) q).hom) ∧
      (∀ {X Y : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : X ⟶ Y) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (pageOneIso Y p q).hom =
          (pageOneIso X p q).hom ≫
            (fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).map f) ∧
      (∀ X : DerivedCategory.Plus (SheafOfModules.{w} O),
        (m (𝟙 X)).sequenceMap = 𝟙 (S X).sequence) ∧
      (∀ {X Y Z : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : X ⟶ Y) (g : Y ⟶ Z),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap) :=
  sorry

end CategoryTheory.Grothendieck
