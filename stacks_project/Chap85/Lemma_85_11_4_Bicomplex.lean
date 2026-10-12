/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import stacks_project.Chap85.Lemma_85_11_3_Complex

/-!
# Čech–injective double complex of an augmentation of ringed sites

In Situation 85.3.3 case A, with an augmentation towards a site `D` as in
Remark 85.4.1 and a ring map `O_D ⟶ a_* O`, a cochain complex `I` of
`O`-modules on `C_total` determines the double complex `A^{p,q} = a_{p,*} I^q_p`
whose horizontal differentials are those of `moduleAugmentationCechComplex`
and whose vertical differentials come from `I`. The associated first-page and
abutment functors on `DerivedCategory.Plus` recover `R^q a_{p,*} K_p` and
`R^n a_* K` as sheaves of `O_D`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory RingedSite ZeroObject
open scoped HomologicalComplex₂ Simplicial

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
variable [(SheafOfModules.restrictScalars.{w}
    (moduleAugmentationHom C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp
      (moduleAugmentationHom C J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
include h_morphism
include h_aug

/-- Canonical derived-category structure on `O`-modules on the total site. -/
instance totalModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O) :=
  Hom.RingPresentation.moduleHasDerivedCategory (topology C J) O

/-- Canonical derived-category structure on `O_D`-modules on the augmentation target. -/
instance augmentationTargetModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{w} O_D) :=
  Hom.RingPresentation.moduleHasDerivedCategory K.toGrothendieck O_D

/-- The component of a morphism of `O`-modules under `n ↦ a_{n,*} (-)_n`. -/
def modulePushforwardCosimplicialMap {F G : SheafOfModules.{w} O} (α : F ⟶ G)
    (n : SimplexCategory) :
    (modulePushforwardCosimplicial C J K u0 O O_D aSharp F).obj n ⟶
      (modulePushforwardCosimplicial C J K u0 O O_D aSharp G).obj n :=
  ((stageMorphism C J O n).comp
      (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.map
    ((stageMorphism C J O n).modulePullback.map α)

/-- Naturality of `modulePushforwardCosimplicialMap` in the simplicial degree. -/
theorem modulePushforwardCosimplicialMap_naturality {F G : SheafOfModules.{w} O}
    (α : F ⟶ G) {n m : SimplexCategory} (φ : n ⟶ m) :
    (modulePushforwardCosimplicial C J K u0 O O_D aSharp F).map φ ≫
        modulePushforwardCosimplicialMap C J K u0 O O_D aSharp α m =
      modulePushforwardCosimplicialMap C J K u0 O O_D aSharp α n ≫
        (modulePushforwardCosimplicial C J K u0 O O_D aSharp G).map φ :=
  sorry

/-- The natural transformation `n ↦ a_{n,*} F_n ⟶ a_{n,*} G_n` induced by `α`. -/
def modulePushforwardCosimplicialNatTrans {F G : SheafOfModules.{w} O} (α : F ⟶ G) :
    modulePushforwardCosimplicial C J K u0 O O_D aSharp F ⟶
      modulePushforwardCosimplicial C J K u0 O O_D aSharp G where
  app n := modulePushforwardCosimplicialMap C J K u0 O O_D aSharp α n
  naturality _ _ φ :=
    modulePushforwardCosimplicialMap_naturality C J K u0 O O_D aSharp α φ

/-- Identity morphisms act as the identity on `modulePushforwardCosimplicial`. -/
theorem modulePushforwardCosimplicialNatTrans_id (F : SheafOfModules.{w} O) :
    modulePushforwardCosimplicialNatTrans C J K u0 O O_D aSharp (𝟙 F) =
      𝟙 (modulePushforwardCosimplicial C J K u0 O O_D aSharp F) :=
  sorry

/-- `modulePushforwardCosimplicialNatTrans` preserves composition. -/
theorem modulePushforwardCosimplicialNatTrans_comp {F G H : SheafOfModules.{w} O}
    (α : F ⟶ G) (β : G ⟶ H) :
    modulePushforwardCosimplicialNatTrans C J K u0 O O_D aSharp (α ≫ β) =
      modulePushforwardCosimplicialNatTrans C J K u0 O O_D aSharp α ≫
        modulePushforwardCosimplicialNatTrans C J K u0 O O_D aSharp β :=
  sorry

/-- Functoriality of `n ↦ a_{n,*} F_n` in the `O`-module `F`. -/
def modulePushforwardCosimplicialFunctor :
    SheafOfModules.{w} O ⥤ CosimplicialObject (SheafOfModules.{w} O_D) where
  obj F := modulePushforwardCosimplicial C J K u0 O O_D aSharp F
  map α := modulePushforwardCosimplicialNatTrans C J K u0 O O_D aSharp α
  map_id := modulePushforwardCosimplicialNatTrans_id C J K u0 O O_D aSharp
  map_comp := modulePushforwardCosimplicialNatTrans_comp C J K u0 O O_D aSharp

/-- The unaugmented Čech cochain functor `F ↦ (a_{0,*} F_0 → a_{1,*} F_1 → ⋯)`. -/
def moduleAugmentationCechComplexFunctor :
    SheafOfModules.{w} O ⥤ CochainComplex (SheafOfModules.{w} O_D) ℕ :=
  modulePushforwardCosimplicialFunctor C J K u0 O O_D aSharp ⋙
    alternatingCofaceMapComplex _

/-- `moduleAugmentationCechComplexFunctor` recovers the unaugmented cochain of
Lemma 85.11.3. -/
theorem moduleAugmentationCechComplexFunctor_obj (F : SheafOfModules.{w} O) :
    (moduleAugmentationCechComplexFunctor C J K u0 O O_D aSharp).obj F =
      moduleAugmentationCechComplex C J K u0 O O_D aSharp F :=
  sorry

/-- The Čech cochain functor of a module augmentation preserves zero morphisms. -/
instance moduleAugmentationCechComplexFunctor_preservesZeroMorphisms :
    (moduleAugmentationCechComplexFunctor C J K u0 O O_D aSharp).PreservesZeroMorphisms :=
  sorry

/-- The Čech cochain functor of a module augmentation is additive. -/
instance moduleAugmentationCechComplexFunctor_additive :
    (moduleAugmentationCechComplexFunctor C J K u0 O O_D aSharp).Additive :=
  sorry

/-- Direct image `a_*` of `O`-modules is additive. -/
instance moduleAugmentationHom_modulePushforward_additive :
    (moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.Additive :=
  ToposHom.modulePushforward_additive
    (moduleAugmentationHom C J K u0 O O_D aSharp)

/-- Direct image `a_*` of `O`-modules preserves zero morphisms. -/
instance moduleAugmentationHom_modulePushforward_preservesZeroMorphisms :
    (moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.PreservesZeroMorphisms :=
  inferInstance

/-- The ℕ-indexed cochain of vertical complexes `p ↦ (q ↦ a_{p,*} I^q_p)`. -/
def moduleAugmentationColumnsFunctor :
    CochainComplex (SheafOfModules.{w} O) ℤ ⥤
      CochainComplex (CochainComplex (SheafOfModules.{w} O_D) ℤ) ℕ :=
  (moduleAugmentationCechComplexFunctor C J K u0 O O_D aSharp).mapHomologicalComplex
      (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℕ)

/-- The Čech–injective double complex functor, reindexed from nonnegative Čech degree. -/
def moduleAugmentationBicomplexFunctor :
    CochainComplex (SheafOfModules.{w} O) ℤ ⥤
      HomologicalComplex₂ (SheafOfModules.{w} O_D) (up ℤ) (up ℤ) :=
  moduleAugmentationColumnsFunctor C J K u0 O O_D aSharp ⋙
    HomologicalComplex₂.CoaugmentedResolution.bicomplexFunctor

/-- The double complex `A^{p,q} = a_{p,*} I^q_p` of a cochain complex of `O`-modules. -/
def moduleAugmentationBicomplex
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    HomologicalComplex₂ (SheafOfModules.{w} O_D) (up ℤ) (up ℤ) :=
  (moduleAugmentationBicomplexFunctor C J K u0 O O_D aSharp).obj I

/-- Nonnegative columns of `moduleAugmentationBicomplex` recover stagewise pushforwards of `I`. -/
theorem moduleAugmentationBicomplex_X_ofNat
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) (p : ℕ) (q : ℤ) :
    ((moduleAugmentationBicomplex C J K u0 O O_D aSharp I).X p).X q =
      ((stageMorphism C J O ⦋p⦌).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.obj
        ((stageMorphism C J O ⦋p⦌).modulePullback.obj (I.X q)) :=
  sorry

/-- Negative Čech columns of `moduleAugmentationBicomplex` vanish. -/
theorem moduleAugmentationBicomplex_isZero_of_neg
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) {p : ℤ} (hp : p < 0) :
    IsZero ((moduleAugmentationBicomplex C J K u0 O O_D aSharp I).X p) :=
  sorry

/-- The coaugmentation source `a_* I^•` as a cochain complex of `O_D`-modules. -/
def moduleAugmentationTotalComplex
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    CochainComplex (SheafOfModules.{w} O_D) ℤ :=
  ((moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.mapHomologicalComplex
      (up ℤ)).obj I

/-- The coaugmentation `a_* I^• ⟶` the zeroth column of the Čech bicomplex. -/
def moduleAugmentationCoaugmentation
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    moduleAugmentationTotalComplex C J K u0 O O_D aSharp I ⟶
      ((moduleAugmentationColumnsFunctor C J K u0 O O_D aSharp).obj I).X 0 where
  f q := moduleAugmentationCechConnect_d₀ C J K u0 O O_D aSharp (I.X q)
  comm' := sorry

/-- The coaugmentation is killed by the first Čech differential. -/
theorem moduleAugmentationCoaugmentation_comp_d
    (I : CochainComplex (SheafOfModules.{w} O) ℤ) :
    moduleAugmentationCoaugmentation C J K u0 O O_D aSharp I ≫
      ((moduleAugmentationColumnsFunctor C J K u0 O O_D aSharp).obj I).d 0 1 = 0 :=
  sorry

/-- Degree-`n` functor sending an `O`-module on `C_total` to `a_{n,*} F_n`. -/
def moduleAugmentationStageGamma (n : ℕ) :
    SheafOfModules.{w} O ⥤ SheafOfModules.{w} O_D :=
  (stageMorphism C J O ⦋n⦌).modulePullback ⋙
    ((stageMorphism C J O ⦋n⦌).comp
      (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward

/-- Stagewise module-augmentation pushforward recovers `a_{n,*} F_n`. -/
theorem moduleAugmentationStageGamma_obj (n : ℕ) (F : SheafOfModules.{w} O) :
    (moduleAugmentationStageGamma C J K u0 O O_D aSharp n).obj F =
      ((stageMorphism C J O ⦋n⦌).comp
          (moduleAugmentationHom C J K u0 O O_D aSharp)).modulePushforward.obj
        ((stageMorphism C J O ⦋n⦌).modulePullback.obj F) :=
  sorry

/-- Stagewise module-augmentation pushforward is additive. -/
instance moduleAugmentationStageGamma_additive (n : ℕ) :
    (moduleAugmentationStageGamma C J K u0 O O_D aSharp n).Additive :=
  sorry

/-- Naturality of the Čech differential in the `O`-module. -/
theorem moduleAugmentationStageGamma_d_naturality (n : ℕ)
    {F G : SheafOfModules.{w} O} (α : F ⟶ G) :
    (moduleAugmentationStageGamma C J K u0 O O_D aSharp n).map α ≫
        (moduleAugmentationCechComplex C J K u0 O O_D aSharp G).d n (n + 1) =
      (moduleAugmentationCechComplex C J K u0 O O_D aSharp F).d n (n + 1) ≫
        (moduleAugmentationStageGamma C J K u0 O O_D aSharp (n + 1)).map α :=
  sorry

/-- The Čech differential as a natural transformation of stagewise pushforwards. -/
def moduleAugmentationStageGamma_d (n : ℕ) :
    moduleAugmentationStageGamma C J K u0 O O_D aSharp n ⟶
      moduleAugmentationStageGamma C J K u0 O O_D aSharp (n + 1) where
  app F := (moduleAugmentationCechComplex C J K u0 O O_D aSharp F).d n (n + 1)
  naturality _ _ α :=
    moduleAugmentationStageGamma_d_naturality C J K u0 O O_D aSharp n α

variable [∀ n : ℕ,
    (moduleAugmentationStageGamma C J K u0 O O_D aSharp n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]

/-- Nonnegative first-page target: `R^q` of `a_{n,*} ((-)_n)`. -/
def moduleAugmentationPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ SheafOfModules.{w} O_D :=
  Functor.RightDerived.Bounded.functor
      (moduleAugmentationStageGamma C J K u0 O O_D aSharp n) ⋙
    DerivedCategory.Plus.homologyFunctor (SheafOfModules.{w} O_D) q

/-- The Čech differential on nonnegative first-page functors. -/
def moduleAugmentationPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    moduleAugmentationPageOneFunctorNonneg C J K u0 O O_D aSharp n q ⟶
      moduleAugmentationPageOneFunctorNonneg C J K u0 O O_D aSharp (n + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map
      (moduleAugmentationStageGamma_d C J K u0 O O_D aSharp n))
    (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{w} O_D) q)

/-- First-page target `K ↦ R^q a_{p,*} K_p`, vanishing for `p < 0`. -/
def moduleAugmentationPageOneFunctor (p q : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ SheafOfModules.{w} O_D :=
  if 0 ≤ p then moduleAugmentationPageOneFunctorNonneg C J K u0 O O_D aSharp p.toNat q
  else
    (Functor.const (DerivedCategory.Plus (SheafOfModules.{w} O))).obj
      (0 : SheafOfModules.{w} O_D)

/-- Nonnegative bidegrees of `moduleAugmentationPageOneFunctor` recover the nonnegative functor. -/
theorem moduleAugmentationPageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q =
      moduleAugmentationPageOneFunctorNonneg C J K u0 O O_D aSharp p.toNat q :=
  sorry

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def moduleAugmentationPageOneDifferential (p q : ℤ) :
    moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q ⟶
      moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (if_pos hp) ≫
      moduleAugmentationPageOneDifferentialNonneg C J K u0 O O_D aSharp p.toNat q ≫
      eqToHom
        (congrArg (moduleAugmentationPageOneFunctorNonneg C J K u0 O O_D aSharp · q)
          (Int.toNat_add_nat hp 1)).symm ≫
      eqToHom (if_pos (Int.add_nonneg hp zero_le_one)).symm
  else
    (0 : moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q ⟶
      moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp (p + 1) q)

/-- First-page sheaves in negative Čech degree vanish. -/
theorem moduleAugmentationPageOneFunctor_neg
    (X : DerivedCategory.Plus (SheafOfModules.{w} O)) {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q).obj X) :=
  sorry

/-- Abutment functor `K ↦ R^n a_* K`. -/
def moduleAugmentationAbutmentFunctor (n : ℤ) :
    DerivedCategory.Plus (SheafOfModules.{w} O) ⥤ SheafOfModules.{w} O_D :=
  Functor.RightDerived.Bounded.functor
      (moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward ⋙
    DerivedCategory.Plus.homologyFunctor (SheafOfModules.{w} O_D) n

/-- Evaluation of `moduleAugmentationAbutmentFunctor` is cohomology of `R a_*`. -/
theorem moduleAugmentationAbutmentFunctor_obj (n : ℤ)
    (X : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    (moduleAugmentationAbutmentFunctor C J K u0 O O_D aSharp n).obj X =
      (DerivedCategory.Plus.homologyFunctor (SheafOfModules.{w} O_D) n).obj
        ((Functor.RightDerived.Bounded.functor
          (moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward).obj X) :=
  sorry

/-- For a bounded-below complex of injectives representing `K`, vertical homology of
`moduleAugmentationBicomplex` recovers the first-page target. -/
theorem moduleAugmentationPageOne_isomorphic_of_injectiveRepresentative
    (I : CochainComplex (SheafOfModules.{w} O) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)]
    (X : DerivedCategory.Plus (SheafOfModules.{w} O))
    (hX : Nonempty (DerivedCategory.Plus.ι.obj X ≅ DerivedCategory.Q.obj I))
    (p q : ℤ) :
    IsIsomorphic
      (HomologicalComplex₂.First.PageOne.entry
        (moduleAugmentationBicomplex C J K u0 O O_D aSharp I) p q)
      ((moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q).obj X) :=
  sorry

/-- The coaugmentation-to-total comparison is a quasi-isomorphism when every term of `I`
is injective. -/
theorem moduleAugmentationToTotal_quasiIso
    [HasCountableCoproducts (SheafOfModules.{w} O_D)]
    [CountableAB4 (SheafOfModules.{w} O_D)]
    (I : CochainComplex (SheafOfModules.{w} O) ℤ)
    [∀ n, Injective (I.X n)] :
    QuasiIso
      (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map
        ((moduleAugmentationColumnsFunctor C J K u0 O O_D aSharp).obj I)
        (moduleAugmentationCoaugmentation C J K u0 O O_D aSharp I)
        (moduleAugmentationCoaugmentation_comp_d C J K u0 O O_D aSharp I)) :=
  sorry

end CategoryTheory.SimplicialSites
