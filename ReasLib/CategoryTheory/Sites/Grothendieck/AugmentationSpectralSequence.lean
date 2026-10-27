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
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationCech

/-!
# Augmentation spectral sequences of abelian sheaves

An augmented simplicial site gives a Čech–injective double complex with terms
`a_{p,*} I^q_p`. Its first page computes derived stage direct images and its
abutment computes the derived direct image on the total site. These spectral
sequences can be chosen simultaneously, compatibly with identities and composition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
open scoped HomologicalComplex₂ Simplicial
open FilteredComplex.SpectralSequence.Realization

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [IsFiberwiseSite F J]
variable [IsAugmentation F J K u0]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck AddCommGrpCat.{w})]

/-- A morphism of abelian sheaves induces the componentwise map of augmentation cosimplicial objects. -/
def fiberPushforwardCosimplicialMap {G H : Sheaf (topology F J) AddCommGrpCat.{w}} (α : G ⟶ H) :
    fiberPushforwardCosimplicial F J K u0 G ⟶ fiberPushforwardCosimplicial F J K u0 H where
  app n := (IsAugmentation.abelianStagePushforward F J K u0 n).map
    ((fiberRestrict F J AddCommGrpCat.{w} n).map α)
  naturality := sorry

/-- The componentwise augmentation cosimplicial map preserves identities. -/
theorem fiberPushforwardCosimplicialMap_id (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    fiberPushforwardCosimplicialMap F J K u0 (𝟙 G) = 𝟙 (fiberPushforwardCosimplicial F J K u0 G) := sorry

/-- The componentwise augmentation cosimplicial map preserves composition. -/
theorem fiberPushforwardCosimplicialMap_comp {G H L : Sheaf (topology F J) AddCommGrpCat.{w}} (α : G ⟶ H) (β : H ⟶ L) :
    fiberPushforwardCosimplicialMap F J K u0 (α ≫ β) =
      fiberPushforwardCosimplicialMap F J K u0 α ≫ fiberPushforwardCosimplicialMap F J K u0 β := sorry

/-- Stagewise direct images form a cosimplicial object functorially in the abelian sheaf. -/
def fiberPushforwardCosimplicialFunctor :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤ CosimplicialObject (Sheaf K.toGrothendieck AddCommGrpCat.{w}) where
  obj G := fiberPushforwardCosimplicial F J K u0 G
  map α := fiberPushforwardCosimplicialMap F J K u0 α
  map_id G := fiberPushforwardCosimplicialMap_id F J K u0 G
  map_comp α β := fiberPushforwardCosimplicialMap_comp F J K u0 α β

/-- The unaugmented Čech cochain functor `G ↦ (a_{0,*} G_0 → a_{1,*} G_1 → ⋯)`. -/
def fiberCechComplexFunctor :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤
      CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℕ :=
  fiberPushforwardCosimplicialFunctor F J K u0 ⋙ alternatingCofaceMapComplex _

/-- `fiberCechComplexFunctor` recovers the augmentation Čech cochain complex. -/
theorem fiberCechComplexFunctor_obj (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (fiberCechComplexFunctor F J K u0).obj G = fiberCechComplex F J K u0 G :=
  sorry

/-- The fiberwise Čech cochain functor of an augmentation preserves zero morphisms. -/
instance fiberCechComplexFunctor_preservesZeroMorphisms :
    (fiberCechComplexFunctor F J K u0).PreservesZeroMorphisms :=
  sorry

/-- The fiberwise Čech cochain functor of an augmentation is additive. -/
instance fiberCechComplexFunctor_additive :
    (fiberCechComplexFunctor F J K u0).Additive :=
  sorry

/-- Fiberwise direct image `a_*` of abelian sheaves is additive. -/
instance fiberAbelianPushforward_additive :
    (IsAugmentation.abelianPushforward F J K u0).Additive :=
  sorry

/-- Fiberwise direct image `a_*` of abelian sheaves preserves zero morphisms. -/
instance fiberAbelianPushforward_preservesZeroMorphisms :
    (IsAugmentation.abelianPushforward F J K u0).PreservesZeroMorphisms :=
  sorry

/-- The ℕ-indexed cochain of vertical complexes `p ↦ (q ↦ a_{p,*} I^q_p)`. -/
def fiberAugmentationColumnsFunctor :
    CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex
        (CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℤ) ℕ :=
  (fiberCechComplexFunctor F J K u0).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℕ)

/-- The fiberwise Čech–injective double complex functor. -/
def fiberAugmentationBicomplexFunctor :
    CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ (Sheaf K.toGrothendieck AddCommGrpCat.{w})
        (up ℤ) (up ℤ) :=
  fiberAugmentationColumnsFunctor F J K u0 ⋙
    HomologicalComplex₂.CoaugmentedResolution.bicomplexFunctor

/-- The double complex `A^{p,q} = a_{p,*} I^q_p` in the fiberwise case. -/
def fiberAugmentationBicomplex
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ) :
    HomologicalComplex₂ (Sheaf K.toGrothendieck AddCommGrpCat.{w})
      (up ℤ) (up ℤ) :=
  (fiberAugmentationBicomplexFunctor F J K u0).obj I

/-- Nonnegative columns of `fiberAugmentationBicomplex` recover stagewise pushforwards of `I`. -/
theorem fiberAugmentationBicomplex_X_ofNat
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (p : ℕ) (q : ℤ) :
    ((fiberAugmentationBicomplex F J K u0 I).X p).X q =
      (IsAugmentation.abelianStagePushforward F J K u0 ⦋p⦌).obj
        ((fiberRestrict F J AddCommGrpCat.{w} ⦋p⦌).obj (I.X q)) :=
  sorry

/-- Negative Čech columns of `fiberAugmentationBicomplex` vanish. -/
theorem fiberAugmentationBicomplex_isZero_of_neg
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    {p : ℤ} (hp : p < 0) :
    IsZero ((fiberAugmentationBicomplex F J K u0 I).X p) :=
  sorry

/-- The coaugmentation source `a_* I^•` as a cochain complex of abelian sheaves on `D`. -/
def fiberAugmentationTotalComplex
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ) :
    CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℤ :=
  ((IsAugmentation.abelianPushforward F J K u0).mapHomologicalComplex (up ℤ)).obj I

/-- The coaugmentation `a_* I^• ⟶` the zeroth column of the fiberwise Čech bicomplex. -/
def fiberAugmentationCoaugmentation
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ) :
    fiberAugmentationTotalComplex F J K u0 I ⟶
      ((fiberAugmentationColumnsFunctor F J K u0).obj I).X 0 where
  f q := IsAugmentation.abelianPushforwardι F J K u0 (I.X q)
  comm' := sorry

/-- The coaugmentation is killed by the first Čech differential. -/
theorem fiberAugmentationCoaugmentation_comp_d
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ) :
    fiberAugmentationCoaugmentation F J K u0 I ≫
      ((fiberAugmentationColumnsFunctor F J K u0).obj I).d 0 1 = 0 :=
  sorry

/-- Degree-`n` functor sending an abelian sheaf on the total fiberwise site to `a_{n,*} G_n`. -/
def fiberAugmentationStageGamma (n : ℕ) :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  fiberRestrict F J AddCommGrpCat.{w} ⦋n⦌ ⋙
    IsAugmentation.abelianStagePushforward F J K u0 ⦋n⦌

/-- Stagewise fiberwise augmentation pushforward recovers `a_{n,*} G_n`. -/
theorem fiberAugmentationStageGamma_obj (n : ℕ)
    (G : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (fiberAugmentationStageGamma F J K u0 n).obj G =
      (IsAugmentation.abelianStagePushforward F J K u0 ⦋n⦌).obj
        ((fiberRestrict F J AddCommGrpCat.{w} ⦋n⦌).obj G) :=
  sorry

/-- Stagewise fiberwise augmentation pushforward is additive. -/
instance fiberAugmentationStageGamma_additive (n : ℕ) :
    (fiberAugmentationStageGamma F J K u0 n).Additive :=
  sorry

/-- The Čech differential as a natural transformation of stagewise fiberwise pushforwards. -/
def fiberAugmentationStageGamma_d (n : ℕ) :
    fiberAugmentationStageGamma F J K u0 n ⟶
      fiberAugmentationStageGamma F J K u0 (n + 1) where
  app G := (fiberCechComplex F J K u0 G).d n (n + 1)
  naturality := sorry

variable [EnoughInjectives (Sheaf (topology F J) AddCommGrpCat.{w})]

/-- Nonnegative first-page target: `R^q` of `a_{n,*} ((-)_n)` in the fiberwise case. -/
def fiberAugmentationPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  Functor.RightDerived.Bounded.functor (fiberAugmentationStageGamma F J K u0 n) ⋙
    DerivedCategory.Plus.homologyFunctor
      (Sheaf K.toGrothendieck AddCommGrpCat.{w}) q

/-- The Čech differential on nonnegative first-page functors in the fiberwise case. -/
def fiberAugmentationPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    fiberAugmentationPageOneFunctorNonneg F J K u0 n q ⟶
      fiberAugmentationPageOneFunctorNonneg F J K u0 (n + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map (fiberAugmentationStageGamma_d F J K u0 n))
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf K.toGrothendieck AddCommGrpCat.{w}) q)

/-- First-page target `K ↦ R^q a_{p,*} K_p`, vanishing for `p < 0`. -/
def fiberAugmentationPageOneFunctor (p q : ℤ) :
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  if 0 ≤ p then fiberAugmentationPageOneFunctorNonneg F J K u0 p.toNat q else
    (Functor.const
      (DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}))).obj
      (0 : Sheaf K.toGrothendieck AddCommGrpCat.{w})

/-- Nonnegative bidegrees of `fiberAugmentationPageOneFunctor` recover the nonnegative functor. -/
theorem fiberAugmentationPageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    fiberAugmentationPageOneFunctor F J K u0 p q =
      fiberAugmentationPageOneFunctorNonneg F J K u0 p.toNat q :=
  sorry

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def fiberAugmentationPageOneDifferential (p q : ℤ) :
    fiberAugmentationPageOneFunctor F J K u0 p q ⟶
      fiberAugmentationPageOneFunctor F J K u0 (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (fiberAugmentationPageOneFunctor_eq_of_nonneg F J K u0 p q hp) ≫
      fiberAugmentationPageOneDifferentialNonneg F J K u0 p.toNat q ≫
      eqToHom
        (congrArg (fiberAugmentationPageOneFunctorNonneg F J K u0 · q)
          (by omega)).symm ≫
      eqToHom
        (fiberAugmentationPageOneFunctor_eq_of_nonneg F J K u0 (p + 1) q
          (by omega)).symm
  else
    (0 : fiberAugmentationPageOneFunctor F J K u0 p q ⟶
      fiberAugmentationPageOneFunctor F J K u0 (p + 1) q)

/-- First-page sheaves in negative Čech degree vanish. -/
theorem fiberAugmentationPageOneFunctor_neg
    (X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((fiberAugmentationPageOneFunctor F J K u0 p q).obj X) :=
  sorry

/-- Abutment functor `K ↦ R^n a_* K` in the fiberwise case. -/
def fiberAugmentationAbutmentFunctor (n : ℤ) :
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  Functor.RightDerived.Bounded.functor
      (IsAugmentation.abelianPushforward F J K u0) ⋙
    DerivedCategory.Plus.homologyFunctor
      (Sheaf K.toGrothendieck AddCommGrpCat.{w}) n

/-- Evaluation of `fiberAugmentationAbutmentFunctor` is cohomology of `R a_*`. -/
theorem fiberAugmentationAbutmentFunctor_obj
    (n : ℤ)
    (X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})) :
    (fiberAugmentationAbutmentFunctor F J K u0 n).obj X =
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf K.toGrothendieck AddCommGrpCat.{w}) n).obj
        ((Functor.RightDerived.Bounded.functor
          (IsAugmentation.abelianPushforward F J K u0)).obj X) :=
  sorry

/-- For a bounded-below complex of injectives representing `K`, vertical homology of
`fiberAugmentationBicomplex` recovers the first-page target. -/
theorem fiberAugmentationPageOne_isomorphic_of_injectiveRepresentative
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)]
    (X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hX : Nonempty
      (DerivedCategory.Plus.ι.obj X ≅ DerivedCategory.Q.obj I))
    (p q : ℤ) :
    IsIsomorphic
      (HomologicalComplex₂.First.PageOne.entry
        (fiberAugmentationBicomplex F J K u0 I) p q)
      ((fiberAugmentationPageOneFunctor F J K u0 p q).obj X) :=
  sorry

/-- The coaugmentation-to-total comparison is a quasi-isomorphism for a bounded-below complex
of injective abelian sheaves. -/
theorem fiberAugmentationToTotal_quasiIso
    [HasCountableCoproducts (Sheaf K.toGrothendieck AddCommGrpCat.{w})]
    [CountableAB4 (Sheaf K.toGrothendieck AddCommGrpCat.{w})]
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)] :
    QuasiIso
      (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map
        ((fiberAugmentationColumnsFunctor F J K u0).obj I)
        (fiberAugmentationCoaugmentation F J K u0 I)
        (fiberAugmentationCoaugmentation_comp_d F J K u0 I)) :=
  sorry

/-- Augmentation spectral sequences can be chosen simultaneously on all bounded-below derived
abelian sheaves, with natural first-page comparisons and identity and composition laws. -/
theorem fiberAugmentationSpectralSequence_functorial :
    ∃ (S : ∀ X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}),
        WithAbutment (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) X)
      (pageOneIso : ∀ (X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})) (p q : ℤ),
        ((S X).sequence.page 1).X (p, q) ≅
          (fiberAugmentationPageOneFunctor F J K u0 p q).obj X)
      (m : ∀ {X Y : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})} (f : X ⟶ Y),
        WithAbutment.Map (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) f (S X) (S Y)),
      (∀ (X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})) (p q : ℤ),
        (pageOneIso X p q).hom ≫ (fiberAugmentationPageOneDifferential F J K u0 p q).app X =
          ((S X).sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso X (p + 1) q).hom) ∧
      (∀ {X Y : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})} (f : X ⟶ Y) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (pageOneIso Y p q).hom =
          (pageOneIso X p q).hom ≫ (fiberAugmentationPageOneFunctor F J K u0 p q).map f) ∧
      (∀ X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}),
        (m (𝟙 X)).sequenceMap = 𝟙 (S X).sequence) ∧
      (∀ {X Y Z : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})} (f : X ⟶ Y) (g : Y ⟶ Z),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap) := sorry

/-- Every bounded-below derived abelian sheaf has a convergent augmentation spectral sequence
whose first page is derived stage direct image with its canonical Čech differential. -/
theorem exists_fiberAugmentationSpectralSequence
    (X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})) :
    ∃ (S : WithAbutment (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) X)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberAugmentationPageOneFunctor F J K u0 p q).obj X),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫
            (fiberAugmentationPageOneDifferential F J K u0 p q).app X =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

end CategoryTheory.Grothendieck
