module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Simplicial.SectionsComplex

/-!
# Čech–injective double complex on a morphism diagram of sites

A cochain complex `I` of abelian sheaves on `C_total`
determines the double complex `A^{p,q} = Γ(C_p, I^q_p)` whose horizontal
differentials are those of `globalSectionsComplex` and whose vertical
differentials come from `I`. The associated first-page functors recover
`H^q(C_p, K_p)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
open scoped HomologicalComplex₂

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The Čech cochain functor on abelian sheaves on `C_total` preserves zero morphisms. -/
instance globalSectionsComplexFunctor_preservesZeroMorphisms :
    (globalSectionsComplexFunctor C J).PreservesZeroMorphisms :=
  sorry

/-- The Čech cochain functor on abelian sheaves on `C_total` is additive. -/
instance globalSectionsComplexFunctor_additive :
    (globalSectionsComplexFunctor C J).Additive :=
  sorry

/-- The ℕ-indexed cochain of vertical complexes `p ↦ (q ↦ Γ(C_p, I^q_p))`. -/
def sectionsColumnsFunctor :
    CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex (CochainComplex AddCommGrpCat.{max u w} ℤ) ℕ :=
  (globalSectionsComplexFunctor C J).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℕ)

/-- The Čech–injective double complex functor, reindexed from nonnegative Čech degree. -/
def sectionsBicomplexFunctor :
    CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ) :=
  sectionsColumnsFunctor C J ⋙ HomologicalComplex₂.CoaugmentedResolution.bicomplexFunctor

/-- The double complex `A^{p,q} = Γ(C_p, I^q_p)` of a cochain complex of abelian sheaves. -/
def sectionsBicomplex
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ) :=
  (sectionsBicomplexFunctor C J).obj I

/-- Nonnegative columns of `sectionsBicomplex` recover stagewise global sections of `I`. -/
theorem sectionsBicomplex_X_ofNat
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (p : ℕ) (q : ℤ) :
    ((sectionsBicomplex C J I).X p).X q =
      (globalSectionsComplex C J (I.X q)).X p :=
  sorry

/-- Negative Čech columns of `sectionsBicomplex` vanish. -/
theorem sectionsBicomplex_isZero_of_neg
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    {p : ℤ} (hp : p < 0) :
    IsZero ((sectionsBicomplex C J I).X p) :=
  sorry

/-- The functor `F ↦ Hom(ℤ, F)`, equivalently `Γ(C_total, F)` after Yoneda. -/
def globalSectionsTotalFunctor :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w} :=
  preadditiveYoneda.flip.obj (op (constantIntegerSheaf (topology C J)))

/-- `globalSectionsTotalFunctor` recovers `globalSectionsTotal`. -/
theorem globalSectionsTotalFunctor_obj
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (globalSectionsTotalFunctor C J).obj F = globalSectionsTotal C J F :=
  sorry

/-- Global sections of the total site, as a Hom functor, preserve zero morphisms. -/
instance globalSectionsTotalFunctor_preservesZeroMorphisms :
    (globalSectionsTotalFunctor C J).PreservesZeroMorphisms :=
  sorry

/-- The coaugmentation source `Γ(C_total, I^•)` as a cochain complex. -/
def sectionsTotalComplex
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ) :
    CochainComplex AddCommGrpCat.{max u w} ℤ :=
  ((globalSectionsTotalFunctor C J).mapHomologicalComplex (up ℤ)).obj I

/-- The coaugmentation `Γ(C_total, I^•) ⟶` the zeroth column of the Čech bicomplex. -/
def sectionsCoaugmentation
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ) :
    sectionsTotalComplex C J I ⟶ ((sectionsColumnsFunctor C J).obj I).X 0 where
  f q := globalSectionsCoaugmentation C J (I.X q)
  comm' := sorry

/-- The coaugmentation is killed by the first Čech differential. -/
theorem sectionsCoaugmentation_comp_d
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ) :
    sectionsCoaugmentation C J I ≫ ((sectionsColumnsFunctor C J).obj I).d 0 1 = 0 :=
  sorry

/-- Degree-`n` functor sending an abelian sheaf on `C_total` to `Γ(C_n, F_n)`. -/
def sectionsStageGamma (n : ℕ) :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w} :=
  globalSectionsComplexFunctor C J ⋙
    HomologicalComplex.eval AddCommGrpCat.{max u w} (up ℕ) n

/-- Stagewise global sections are additive. -/
instance sectionsStageGamma_additive (n : ℕ) :
    (sectionsStageGamma C J n).Additive :=
  sorry

/-- The Čech differential as a natural transformation of stagewise global sections. -/
def sectionsStageGamma_d (n : ℕ) :
    sectionsStageGamma C J n ⟶ sectionsStageGamma C J (n + 1) where
  app F := (globalSectionsComplex C J F).d n (n + 1)
  naturality := sorry

variable [∀ n : ℕ,
    (sectionsStageGamma C J n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]
variable [(globalSectionsTotalFunctor C J).Additive]
variable [(globalSectionsTotalFunctor C J).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]

/-- Nonnegative first-page target: `H^q` of the derived functor of `Γ(C_n, (-)_n)`. -/
def pageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (sectionsStageGamma C J n) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q

/-- The Čech differential on nonnegative first-page functors. -/
def pageOneDifferentialNonneg (n : ℕ) (q : ℤ) :
    pageOneFunctorNonneg C J n q ⟶ pageOneFunctorNonneg C J (n + 1) q :=
  whiskerRight
    (Functor.RightDerived.Bounded.map (sectionsStageGamma_d C J n))
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} q)

/-- First-page target `K ↦ H^q(C_p, K_p)`, vanishing for `p < 0`. -/
def pageOneFunctor (p q : ℤ) :
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w} :=
  if 0 ≤ p then pageOneFunctorNonneg C J p.toNat q else
    (Functor.const
      (DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}))).obj
      (0 : AddCommGrpCat.{max u w})

/-- Nonnegative bidegrees of `pageOneFunctor` recover `pageOneFunctorNonneg`. -/
theorem pageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    pageOneFunctor C J p q = pageOneFunctorNonneg C J p.toNat q := by
  simp only [pageOneFunctor, if_pos hp]

/-- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
def pageOneDifferential (p q : ℤ) :
    pageOneFunctor C J p q ⟶ pageOneFunctor C J (p + 1) q :=
  if hp : 0 ≤ p then
    eqToHom (pageOneFunctor_eq_of_nonneg C J p q hp) ≫
      pageOneDifferentialNonneg C J p.toNat q ≫
      eqToHom (congrArg (pageOneFunctorNonneg C J · q)
        (by omega)).symm ≫
      eqToHom (pageOneFunctor_eq_of_nonneg C J (p + 1) q (by omega)).symm
  else
    (0 : pageOneFunctor C J p q ⟶ pageOneFunctor C J (p + 1) q)

/-- First-page groups in negative Čech degree vanish. -/
theorem pageOneFunctor_neg
    (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ) :
    IsZero ((pageOneFunctor C J p q).obj K) :=
  sorry

/-- Abutment functor `K ↦ H^n(C_total, K)`. -/
def abutmentFunctor (n : ℤ) :
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w} :=
  Functor.RightDerived.Bounded.functor (globalSectionsTotalFunctor C J) ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n

/-- Evaluation of `abutmentFunctor` is cohomology of `RΓ(C_total, -)`. -/
theorem abutmentFunctor_obj
    (n : ℤ)
    (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (abutmentFunctor C J n).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((Functor.RightDerived.Bounded.functor
          (globalSectionsTotalFunctor C J)).obj K) :=
  sorry

/-- For a bounded-below complex of injectives representing `K`, vertical homology of
`sectionsBicomplex` recovers the first-page target. -/
theorem pageOne_isomorphic_of_injectiveRepresentative
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)]
    (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hK : Nonempty
      (DerivedCategory.Plus.ι.obj K ≅ DerivedCategory.Q.obj I))
    (p q : ℤ) :
    IsIsomorphic
      (HomologicalComplex₂.First.PageOne.entry (sectionsBicomplex C J I) p q)
      ((pageOneFunctor C J p q).obj K) :=
  sorry

/-- The coaugmentation-to-total comparison is a quasi-isomorphism when every term of `I`
is injective. -/
theorem sectionsToTotal_quasiIso
    [HasCountableCoproducts AddCommGrpCat.{max u w}]
    [CountableAB4 AddCommGrpCat.{max u w}]
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [∀ n, Injective (I.X n)] :
    QuasiIso
      (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map
        ((sectionsColumnsFunctor C J).obj I)
        (sectionsCoaugmentation C J I)
        (sectionsCoaugmentation_comp_d C J I)) :=
  sorry

end CategoryTheory.SimplicialSites
