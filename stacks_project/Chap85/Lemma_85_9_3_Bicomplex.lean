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
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap85.Lemma_85_9_2_Complex

/-!
# Čech–injective double complex of an augmentation of sites

In Situation 85.3.3 case A, with an augmentation towards a site `D` as in
Remark 85.4.1, a cochain complex `I` of abelian sheaves on `C_total` determines
the double complex `A^{p,q} = a_{p,*} I^q_p` whose horizontal differentials are
those of `cechComplex` and whose vertical differentials come from `I`. The
associated first-page and abutment functors on `DerivedCategory.Plus` recover
`R^q a_{p,*} K_p` and `R^n a_* K` as abelian sheaves on `D`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
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
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck AddCommGrpCat.{w})]

/-- Functoriality of `n ↦ a_{n,*} F_n` in the abelian sheaf `F`. -/
def pushforwardCosimplicialFunctor :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤
      CosimplicialObject (Sheaf K.toGrothendieck AddCommGrpCat.{w}) where
  obj F := pushforwardCosimplicial C J K u0 F
  map {F G} α :=
    { app := fun n ↦
        (IsAugmentation.abelianStagePushforward C J K u0 n).map
          ((stageRestrict C J AddCommGrpCat.{w} n).map α)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The unaugmented Čech cochain functor `F ↦ (a_{0,*} F_0 → a_{1,*} F_1 → ⋯)`. -/
def cechComplexFunctor :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤
      CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℕ :=
  pushforwardCosimplicialFunctor C J K u0 ⋙ alternatingCofaceMapComplex _

/-- `cechComplexFunctor` recovers the unaugmented cochain of Lemma 85.9.2. -/
theorem cechComplexFunctor_obj (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (cechComplexFunctor C J K u0).obj F = cechComplex C J K u0 F :=
  sorry

/-- The Čech cochain functor of an augmentation preserves zero morphisms. -/
instance cechComplexFunctor_preservesZeroMorphisms :
    (cechComplexFunctor C J K u0).PreservesZeroMorphisms :=
  sorry

/-- The Čech cochain functor of an augmentation is additive. -/
instance cechComplexFunctor_additive :
    (cechComplexFunctor C J K u0).Additive :=
  sorry

/-- Direct image `a_*` of abelian sheaves is additive. -/
instance abelianPushforward_additive :
    (IsAugmentation.abelianPushforward C J K u0).Additive :=
  sorry

/-- Direct image `a_*` of abelian sheaves preserves zero morphisms. -/
instance abelianPushforward_preservesZeroMorphisms :
    (IsAugmentation.abelianPushforward C J K u0).PreservesZeroMorphisms :=
  sorry

/-- The ℕ-indexed cochain of vertical complexes `p ↦ (q ↦ a_{p,*} I^q_p)`. -/
def augmentationColumnsFunctor :
    CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex
        (CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℤ) ℕ :=
  (cechComplexFunctor C J K u0).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℕ)

/-- The Čech–injective double complex functor, reindexed from nonnegative Čech degree. -/
def augmentationBicomplexFunctor :
    CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ (Sheaf K.toGrothendieck AddCommGrpCat.{w})
        (up ℤ) (up ℤ) :=
  augmentationColumnsFunctor C J K u0 ⋙
    HomologicalComplex₂.CoaugmentedResolution.bicomplexFunctor

/-- The double complex `A^{p,q} = a_{p,*} I^q_p` of a cochain complex of abelian sheaves. -/
def augmentationBicomplex
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ) :
    HomologicalComplex₂ (Sheaf K.toGrothendieck AddCommGrpCat.{w})
      (up ℤ) (up ℤ) :=
  (augmentationBicomplexFunctor C J K u0).obj I

/-- Nonnegative columns of `augmentationBicomplex` recover stagewise pushforwards of `I`. -/
theorem augmentationBicomplex_X_ofNat
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (p : ℕ) (q : ℤ) :
    ((augmentationBicomplex C J K u0 I).X p).X q =
      (IsAugmentation.abelianStagePushforward C J K u0 ⦋p⦌).obj
        ((stageRestrict C J AddCommGrpCat.{w} ⦋p⦌).obj (I.X q)) :=
  sorry

/-- Negative Čech columns of `augmentationBicomplex` vanish. -/
theorem augmentationBicomplex_isZero_of_neg
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    {p : ℤ} (hp : p < 0) :
    IsZero ((augmentationBicomplex C J K u0 I).X p) :=
  sorry

/-- The coaugmentation source `a_* I^•` as a cochain complex of abelian sheaves on `D`. -/
def augmentationTotalComplex
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ) :
    CochainComplex (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ℤ :=
  ((IsAugmentation.abelianPushforward C J K u0).mapHomologicalComplex (up ℤ)).obj I

/-- The coaugmentation `a_* I^• ⟶` the zeroth column of the Čech bicomplex. -/
def augmentationCoaugmentation
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ) :
    augmentationTotalComplex C J K u0 I ⟶
      ((augmentationColumnsFunctor C J K u0).obj I).X 0 where
  f q := IsAugmentation.abelianPushforwardι C J K u0 (I.X q)
  comm' := sorry

/-- The coaugmentation is killed by the first Čech differential. -/
theorem augmentationCoaugmentation_comp_d
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ) :
    augmentationCoaugmentation C J K u0 I ≫
      ((augmentationColumnsFunctor C J K u0).obj I).d 0 1 = 0 :=
  sorry

/-- Degree-`n` functor sending an abelian sheaf on `C_total` to `a_{n,*} F_n`. -/
def augmentationStageGamma (n : ℕ) :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  stageRestrict C J AddCommGrpCat.{w} ⦋n⦌ ⋙
    IsAugmentation.abelianStagePushforward C J K u0 ⦋n⦌

/-- Stagewise augmentation pushforward recovers `a_{n,*} F_n`. -/
theorem augmentationStageGamma_obj (n : ℕ)
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (augmentationStageGamma C J K u0 n).obj F =
      (IsAugmentation.abelianStagePushforward C J K u0 ⦋n⦌).obj
        ((stageRestrict C J AddCommGrpCat.{w} ⦋n⦌).obj F) :=
  sorry

/-- Stagewise augmentation pushforward is additive. -/
instance augmentationStageGamma_additive (n : ℕ) :
    (augmentationStageGamma C J K u0 n).Additive :=
  sorry

/-- The Čech differential as a natural transformation of stagewise pushforwards. -/
def augmentationStageGamma_d (n : ℕ) :
    augmentationStageGamma C J K u0 n ⟶ augmentationStageGamma C J K u0 (n + 1) where
  app F := (cechComplex C J K u0 F).d n (n + 1)
  naturality := sorry

variable [∀ n : ℕ,
    (augmentationStageGamma C J K u0 n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (topology C J) AddCommGrpCat.{w}))]
variable [(IsAugmentation.abelianPushforward C J K u0).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]

/-- Nonnegative first-page target: `R^q` of `a_{n,*} ((-)_n)`. -/
def augmentationPageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  Functor.RightDerived.Bounded.functor (augmentationStageGamma C J K u0 n) ⋙
    DerivedCategory.Plus.homologyFunctor
      (Sheaf K.toGrothendieck AddCommGrpCat.{w}) q

/-- The Čech differential on nonnegative first-page functors. -/
def augmentationPageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    augmentationPageOneFunctorNonneg C J K u0 n q ⟶
      augmentationPageOneFunctorNonneg C J K u0 (n + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map (augmentationStageGamma_d C J K u0 n))
    (DerivedCategory.Plus.homologyFunctor
      (Sheaf K.toGrothendieck AddCommGrpCat.{w}) q)

/-- Successor of a nonnegative integer remains nonnegative. -/
theorem augmentation_nonneg_succ {n : ℤ} (hn : 0 ≤ n) : 0 ≤ n + 1 :=
  sorry

/-- `toNat` converts a successor of a nonnegative integer into a successor of naturals. -/
theorem augmentation_toNat_succ_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    (n + 1).toNat = n.toNat + 1 :=
  sorry

/-- First-page target `K ↦ R^q a_{p,*} K_p`, vanishing for `p < 0`. -/
def augmentationPageOneFunctor (p q : ℤ) :
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  if 0 ≤ p then augmentationPageOneFunctorNonneg C J K u0 p.toNat q else
    (Functor.const
      (DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}))).obj
      (0 : Sheaf K.toGrothendieck AddCommGrpCat.{w})

/-- Nonnegative bidegrees of `augmentationPageOneFunctor` recover the nonnegative functor. -/
theorem augmentationPageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    augmentationPageOneFunctor C J K u0 p q =
      augmentationPageOneFunctorNonneg C J K u0 p.toNat q :=
  sorry

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def augmentationPageOneDifferential (p q : ℤ) :
    augmentationPageOneFunctor C J K u0 p q ⟶
      augmentationPageOneFunctor C J K u0 (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (augmentationPageOneFunctor_eq_of_nonneg C J K u0 p q hp) ≫
      augmentationPageOneDifferentialNonneg C J K u0 p.toNat q ≫
      eqToHom
        (congrArg (augmentationPageOneFunctorNonneg C J K u0 · q)
          (augmentation_toNat_succ_of_nonneg hp)).symm ≫
      eqToHom
        (augmentationPageOneFunctor_eq_of_nonneg C J K u0 (p + 1) q
          (augmentation_nonneg_succ hp)).symm
  else
    (0 : augmentationPageOneFunctor C J K u0 p q ⟶
      augmentationPageOneFunctor C J K u0 (p + 1) q)

/-- First-page sheaves in negative Čech degree vanish. -/
theorem augmentationPageOneFunctor_neg
    (X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((augmentationPageOneFunctor C J K u0 p q).obj X) :=
  sorry

/-- Abutment functor `K ↦ R^n a_* K`. -/
def augmentationAbutmentFunctor (n : ℤ) :
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      Sheaf K.toGrothendieck AddCommGrpCat.{w} :=
  Functor.RightDerived.Bounded.functor
      (IsAugmentation.abelianPushforward C J K u0) ⋙
    DerivedCategory.Plus.homologyFunctor
      (Sheaf K.toGrothendieck AddCommGrpCat.{w}) n

/-- Evaluation of `augmentationAbutmentFunctor` is cohomology of `R a_*`. -/
theorem augmentationAbutmentFunctor_obj
    (n : ℤ)
    (X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (augmentationAbutmentFunctor C J K u0 n).obj X =
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf K.toGrothendieck AddCommGrpCat.{w}) n).obj
        ((Functor.RightDerived.Bounded.functor
          (IsAugmentation.abelianPushforward C J K u0)).obj X) :=
  sorry

/-- For a bounded-below complex of injectives representing `K`, vertical homology of
`augmentationBicomplex` recovers the first-page target. -/
theorem augmentationPageOne_isomorphic_of_injectiveRepresentative
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)]
    (X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hX : Nonempty
      (DerivedCategory.Plus.ι.obj X ≅ DerivedCategory.Q.obj I))
    (p q : ℤ) :
    IsIsomorphic
      (HomologicalComplex₂.First.PageOne.entry
        (augmentationBicomplex C J K u0 I) p q)
      ((augmentationPageOneFunctor C J K u0 p q).obj X) :=
  sorry

/-- The coaugmentation-to-total comparison is a quasi-isomorphism when every term of `I`
is injective. -/
theorem augmentationToTotal_quasiIso
    [HasCountableCoproducts (Sheaf K.toGrothendieck AddCommGrpCat.{w})]
    [CountableAB4 (Sheaf K.toGrothendieck AddCommGrpCat.{w})]
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [∀ n, Injective (I.X n)] :
    QuasiIso
      (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map
        ((augmentationColumnsFunctor C J K u0).obj I)
        (augmentationCoaugmentation C J K u0 I)
        (augmentationCoaugmentation_comp_d C J K u0 I)) :=
  sorry

end CategoryTheory.SimplicialSites
