/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Bicomplex

/-!
# Čech–injective double complex on a morphism diagram of sites

In Situation 85.3.3 case A, a cochain complex `I` of abelian sheaves on `C_total`
determines the double complex `A^{p,q} = Γ(C_p, I^q_p)` whose horizontal
differentials are those of `globalSectionsComplex` and whose vertical
differentials come from `I`. The associated first-page and abutment functors on
`DerivedCategory.Plus` recover `H^q(C_p, K_p)` and `H^n(C_total, K)`.
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

/- The Čech cochain functor on abelian sheaves on `C_total` preserves zero morphisms. -/
#check (CategoryTheory.SimplicialSites.globalSectionsComplexFunctor_preservesZeroMorphisms C J :
  (globalSectionsComplexFunctor C J).PreservesZeroMorphisms)

/- The Čech cochain functor on abelian sheaves on `C_total` is additive. -/
#check (CategoryTheory.SimplicialSites.globalSectionsComplexFunctor_additive C J :
  (globalSectionsComplexFunctor C J).Additive)

/- The ℕ-indexed cochain of vertical complexes `p ↦ (q ↦ Γ(C_p, I^q_p))`. -/
#check (CategoryTheory.SimplicialSites.sectionsColumnsFunctor C J :
  CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex (CochainComplex AddCommGrpCat.{max u w} ℤ) ℕ)

/- The Čech–injective double complex functor, reindexed from nonnegative Čech degree. -/
#check (CategoryTheory.SimplicialSites.sectionsBicomplexFunctor C J :
  CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ))

/- The double complex `A^{p,q} = Γ(C_p, I^q_p)` of a cochain complex of abelian sheaves. -/
#check (CategoryTheory.SimplicialSites.sectionsBicomplex C J :
  ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ))

/- Nonnegative columns of `sectionsBicomplex` recover stagewise global sections of `I`. -/
#check (CategoryTheory.SimplicialSites.sectionsBicomplex_X_ofNat C J :
  ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (p : ℕ) (q : ℤ),
    ((sectionsBicomplex C J I).X p).X q =
      (globalSectionsComplex C J (I.X q)).X p)

/- Negative Čech columns of `sectionsBicomplex` vanish. -/
#check (CategoryTheory.SimplicialSites.sectionsBicomplex_isZero_of_neg C J :
  ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    {p : ℤ} (hp : p < 0),
    IsZero ((sectionsBicomplex C J I).X p))

/- The functor `F ↦ Hom(ℤ, F)`, equivalently `Γ(C_total, F)` after Yoneda. -/
#check (CategoryTheory.SimplicialSites.globalSectionsTotalFunctor C J :
  Sheaf (topology C J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w})

/- `globalSectionsTotalFunctor` recovers `globalSectionsTotal`. -/
#check (CategoryTheory.SimplicialSites.globalSectionsTotalFunctor_obj C J :
  ∀ (F : Sheaf (topology C J) AddCommGrpCat.{w}),
    (globalSectionsTotalFunctor C J).obj F = globalSectionsTotal C J F)

/- Global sections of the total site, as a Hom functor, preserve zero morphisms. -/
#check (CategoryTheory.SimplicialSites.globalSectionsTotalFunctor_preservesZeroMorphisms C J :
  (globalSectionsTotalFunctor C J).PreservesZeroMorphisms)

/- The coaugmentation source `Γ(C_total, I^•)` as a cochain complex. -/
#check (CategoryTheory.SimplicialSites.sectionsTotalComplex C J :
  ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    CochainComplex AddCommGrpCat.{max u w} ℤ)

/- The coaugmentation `Γ(C_total, I^•) ⟶` the zeroth column of the Čech bicomplex. -/
#check (CategoryTheory.SimplicialSites.sectionsCoaugmentation C J :
  ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    sectionsTotalComplex C J I ⟶ ((sectionsColumnsFunctor C J).obj I).X 0)

/- The coaugmentation is killed by the first Čech differential. -/
#check (CategoryTheory.SimplicialSites.sectionsCoaugmentation_comp_d C J :
  ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    sectionsCoaugmentation C J I ≫ ((sectionsColumnsFunctor C J).obj I).d 0 1 = 0)

/- Degree-`n` functor sending an abelian sheaf on `C_total` to `Γ(C_n, F_n)`. -/
#check (CategoryTheory.SimplicialSites.sectionsStageGamma C J :
  ∀ (n : ℕ),
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w})

/- Stagewise global sections are additive. -/
#check (CategoryTheory.SimplicialSites.sectionsStageGamma_additive C J :
  ∀ (n : ℕ),
    (sectionsStageGamma C J n).Additive)

/- The Čech differential as a natural transformation of stagewise global sections. -/
#check (CategoryTheory.SimplicialSites.sectionsStageGamma_d C J :
  ∀ (n : ℕ),
    sectionsStageGamma C J n ⟶ sectionsStageGamma C J (n + 1))

variable [∀ n : ℕ,
    (sectionsStageGamma C J n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]
variable [(globalSectionsTotalFunctor C J).Additive]
variable [(globalSectionsTotalFunctor C J).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]

/- Nonnegative first-page target: `H^q` of the derived functor of `Γ(C_n, (-)_n)`. -/
#check (CategoryTheory.SimplicialSites.pageOneFunctorNonneg C J :
  ∀ (n : ℕ) (q : ℤ),
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w})

/- The Čech differential on nonnegative first-page functors. -/
#check (CategoryTheory.SimplicialSites.pageOneDifferentialNonneg C J :
  ∀ (n : ℕ) (q : ℤ),
    pageOneFunctorNonneg C J n q ⟶ pageOneFunctorNonneg C J (n + 1) q)

/- Successor of a nonnegative integer remains nonnegative. -/
theorem nonneg_succ {n : ℤ} (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  omega

/- `toNat` converts a successor of a nonnegative integer into a successor of naturals. -/
theorem toNat_succ_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    (n + 1).toNat = n.toNat + 1 := by
  omega

/- First-page target `K ↦ H^q(C_p, K_p)`, vanishing for `p < 0`. -/
#check (CategoryTheory.SimplicialSites.pageOneFunctor C J :
  ∀ (p q : ℤ),
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w})

/- Nonnegative bidegrees of `pageOneFunctor` recover `pageOneFunctorNonneg`. -/
#check (CategoryTheory.SimplicialSites.pageOneFunctor_eq_of_nonneg C J :
  ∀ (p q : ℤ) (hp : 0 ≤ p),
    pageOneFunctor C J p q = pageOneFunctorNonneg C J p.toNat q)

/- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
#check (CategoryTheory.SimplicialSites.pageOneDifferential C J :
  ∀ (p q : ℤ),
    pageOneFunctor C J p q ⟶ pageOneFunctor C J (p + 1) q)

/- First-page groups in negative Čech degree vanish. -/
#check (CategoryTheory.SimplicialSites.pageOneFunctor_neg C J :
  ∀ (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ),
    IsZero ((pageOneFunctor C J p q).obj K))

/- Abutment functor `K ↦ H^n(C_total, K)`. -/
#check (CategoryTheory.SimplicialSites.abutmentFunctor C J :
  ∀ (n : ℤ),
    DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w})

/- Evaluation of `abutmentFunctor` is cohomology of `RΓ(C_total, -)`. -/
#check (CategoryTheory.SimplicialSites.abutmentFunctor_obj C J :
  ∀ (n : ℤ)
    (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})),
    (abutmentFunctor C J n).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((Functor.RightDerived.Bounded.functor
          (globalSectionsTotalFunctor C J)).obj K))

/- For a bounded-below complex of injectives representing `K`, vertical homology of
`sectionsBicomplex` recovers the first-page target. -/
#check (CategoryTheory.SimplicialSites.pageOne_isomorphic_of_injectiveRepresentative C J :
  ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)]
    (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hK : Nonempty
      (DerivedCategory.Plus.ι.obj K ≅ DerivedCategory.Q.obj I))
    (p q : ℤ),
    IsIsomorphic
      (HomologicalComplex₂.First.PageOne.entry (sectionsBicomplex C J I) p q)
      ((pageOneFunctor C J p q).obj K))

/- The coaugmentation-to-total comparison is a quasi-isomorphism when every term of `I`
is injective. -/
#check (CategoryTheory.SimplicialSites.sectionsToTotal_quasiIso C J :
  ∀ [HasCountableCoproducts AddCommGrpCat.{max u w}]
    [CountableAB4 AddCommGrpCat.{max u w}]
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [∀ n, Injective (I.X n)],
    QuasiIso
      (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map
        ((sectionsColumnsFunctor C J).obj I)
        (sectionsCoaugmentation C J I)
        (sectionsCoaugmentation_comp_d C J I)))

end CategoryTheory.SimplicialSites
