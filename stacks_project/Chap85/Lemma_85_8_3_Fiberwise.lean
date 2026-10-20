/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Grothendieck.SpectralSequence

/-!
# Čech–injective double complex on a fiberwise simplicial site

In Situation 85.3.3 case B, a cochain complex `I` of abelian sheaves on the total
fiberwise site determines the double complex `A^{p,q} = Γ(C_p, I^q_p)` whose
horizontal differentials are those of `fiberSectionsComplex`. The associated
first-page and abutment functors on `DerivedCategory.Plus` recover
`H^q(C_p, K_p)` and `H^n(C_total, K)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex ComplexShape DerivedCategory ZeroObject
open scoped HomologicalComplex₂

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/- The Čech cochain functor on abelian sheaves on the total fiberwise site preserves
zero morphisms. -/
#check (CategoryTheory.Grothendieck.fiberSectionsComplexFunctor_preservesZeroMorphisms F J :
  (fiberSectionsComplexFunctor F J).PreservesZeroMorphisms)

/- The Čech cochain functor on abelian sheaves on the total fiberwise site is additive. -/
#check (CategoryTheory.Grothendieck.fiberSectionsComplexFunctor_additive F J :
  (fiberSectionsComplexFunctor F J).Additive)

/- The ℕ-indexed cochain of vertical complexes `p ↦ (q ↦ Γ(C_p, I^q_p))`. -/
#check (CategoryTheory.Grothendieck.fiberSectionsColumnsFunctor F J :
  CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex (CochainComplex AddCommGrpCat.{max u w} ℤ) ℕ)

/- The Čech–injective double complex functor, reindexed from nonnegative Čech degree. -/
#check (CategoryTheory.Grothendieck.fiberSectionsBicomplexFunctor F J :
  CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ))

/- The double complex `A^{p,q} = Γ(C_p, I^q_p)` of a cochain complex of abelian sheaves. -/
#check (CategoryTheory.Grothendieck.fiberSectionsBicomplex F J :
  ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex₂ AddCommGrpCat.{max u w} (up ℤ) (up ℤ))

/- Nonnegative columns of `fiberSectionsBicomplex` recover stagewise global sections of `I`. -/
#check (CategoryTheory.Grothendieck.fiberSectionsBicomplex_X_ofNat F J :
  ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (p : ℕ) (q : ℤ),
    ((fiberSectionsBicomplex F J I).X p).X q =
      (fiberSectionsComplex F J (I.X q)).X p)

/- Negative Čech columns of `fiberSectionsBicomplex` vanish. -/
#check (CategoryTheory.Grothendieck.fiberSectionsBicomplex_isZero_of_neg F J :
  ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    {p : ℤ} (hp : p < 0),
    IsZero ((fiberSectionsBicomplex F J I).X p))

/- The functor `G ↦ Hom(ℤ, G)`, equivalently `Γ(C_total, G)` after Yoneda. -/
#check (CategoryTheory.Grothendieck.fiberSectionsTotalFunctor F J :
  Sheaf (topology F J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w})

/- `fiberSectionsTotalFunctor` recovers `fiberSectionsTotal`. -/
#check (CategoryTheory.Grothendieck.fiberSectionsTotalFunctor_obj F J :
  ∀ (G : Sheaf (topology F J) AddCommGrpCat.{w}),
    (fiberSectionsTotalFunctor F J).obj G = fiberSectionsTotal F J G)

/- Global sections of the total fiberwise site, as a Hom functor, preserve zero morphisms. -/
#check (CategoryTheory.Grothendieck.fiberSectionsTotalFunctor_preservesZeroMorphisms F J :
  (fiberSectionsTotalFunctor F J).PreservesZeroMorphisms)

/- The coaugmentation source `Γ(C_total, I^•)` as a cochain complex. -/
#check (CategoryTheory.Grothendieck.fiberSectionsTotalComplex F J :
  ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    CochainComplex AddCommGrpCat.{max u w} ℤ)

/- The coaugmentation `Γ(C_total, I^•) ⟶` the zeroth column of the Čech bicomplex. -/
#check (CategoryTheory.Grothendieck.fiberSectionsBicomplexCoaugmentation F J :
  ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    fiberSectionsTotalComplex F J I ⟶
      ((fiberSectionsColumnsFunctor F J).obj I).X 0)

/- The coaugmentation is killed by the first Čech differential. -/
#check (CategoryTheory.Grothendieck.fiberSectionsBicomplexCoaugmentation_comp_d F J :
  ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    fiberSectionsBicomplexCoaugmentation F J I ≫
      ((fiberSectionsColumnsFunctor F J).obj I).d 0 1 = 0)

/- Degree-`n` functor sending an abelian sheaf on `C_total` to `Γ(C_n, G_n)`. -/
#check (CategoryTheory.Grothendieck.fiberSectionsStageGamma F J :
  ∀ (n : ℕ),
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤ AddCommGrpCat.{max u w})

/- Stagewise global sections are additive. -/
#check (CategoryTheory.Grothendieck.fiberSectionsStageGamma_additive F J :
  ∀ (n : ℕ),
    (fiberSectionsStageGamma F J n).Additive)

/- The Čech differential as a natural transformation of stagewise global sections. -/
#check (CategoryTheory.Grothendieck.fiberSectionsStageGamma_d F J :
  ∀ (n : ℕ),
    fiberSectionsStageGamma F J n ⟶ fiberSectionsStageGamma F J (n + 1))

variable [∀ n : ℕ,
    (fiberSectionsStageGamma F J n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [(fiberSectionsTotalFunctor F J).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]

/- Nonnegative first-page target: `H^q` of the derived functor of `Γ(C_n, (-)_n)`. -/
#check (CategoryTheory.Grothendieck.fiberPageOneFunctorNonneg F J :
  ∀ (n : ℕ) (q : ℤ),
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w})

/- The Čech differential on nonnegative first-page functors. -/
#check (CategoryTheory.Grothendieck.fiberPageOneDifferentialNonneg F J :
  ∀ (n : ℕ) (q : ℤ),
    fiberPageOneFunctorNonneg F J n q ⟶ fiberPageOneFunctorNonneg F J (n + 1) q)

/- Successor of a nonnegative integer remains nonnegative. -/
theorem fiber_nonneg_succ {n : ℤ} (hn : 0 ≤ n) : 0 ≤ n + 1 := by
  omega

/- `toNat` converts a successor of a nonnegative integer into a successor of naturals. -/
theorem fiber_toNat_succ_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    (n + 1).toNat = n.toNat + 1 := by
  omega

/- First-page target `K ↦ H^q(C_p, K_p)`, vanishing for `p < 0`. -/
#check (CategoryTheory.Grothendieck.fiberPageOneFunctor F J :
  ∀ (p q : ℤ),
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w})

/- Nonnegative bidegrees of `fiberPageOneFunctor` recover `fiberPageOneFunctorNonneg`. -/
#check (CategoryTheory.Grothendieck.fiberPageOneFunctor_eq_of_nonneg F J :
  ∀ (p q : ℤ) (hp : 0 ≤ p),
    fiberPageOneFunctor F J p q = fiberPageOneFunctorNonneg F J p.toNat q)

/- The first-page differential `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`. -/
#check (CategoryTheory.Grothendieck.fiberPageOneDifferential F J :
  ∀ (p q : ℤ),
    fiberPageOneFunctor F J p q ⟶ fiberPageOneFunctor F J (p + 1) q)

/- First-page groups in negative Čech degree vanish. -/
#check (CategoryTheory.Grothendieck.fiberPageOneFunctor_neg F J :
  ∀ (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}))
    {p : ℤ} (hp : p < 0) (q : ℤ),
    IsZero ((fiberPageOneFunctor F J p q).obj K))

/- Abutment functor `K ↦ H^n(C_total, K)`. -/
#check (CategoryTheory.Grothendieck.fiberAbutmentFunctor F J :
  ∀ (n : ℤ),
    DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      AddCommGrpCat.{max u w})

/- Evaluation of `fiberAbutmentFunctor` is cohomology of `RΓ(C_total, -)`. -/
#check (CategoryTheory.Grothendieck.fiberAbutmentFunctor_obj F J :
  ∀ (n : ℤ)
    (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})),
    (fiberAbutmentFunctor F J n).obj K =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u w} n).obj
        ((Functor.RightDerived.Bounded.functor
          (fiberSectionsTotalFunctor F J)).obj K))

/- For a bounded-below complex of injectives representing `K`, vertical homology of
`fiberSectionsBicomplex` recovers the first-page target. -/
#check (CategoryTheory.Grothendieck.fiberPageOne_isomorphic_of_injectiveRepresentative F J :
  ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    (hI : CochainComplex.plus _ I) [∀ n, Injective (I.X n)]
    (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hK : Nonempty
      (DerivedCategory.Plus.ι.obj K ≅ DerivedCategory.Q.obj I))
    (p q : ℤ),
    IsIsomorphic
      (HomologicalComplex₂.First.PageOne.entry (fiberSectionsBicomplex F J I) p q)
      ((fiberPageOneFunctor F J p q).obj K))

/- The coaugmentation-to-total comparison is a quasi-isomorphism when every term of `I`
is injective. -/
#check (CategoryTheory.Grothendieck.fiberSectionsToTotal_quasiIso F J :
  ∀ [HasCountableCoproducts AddCommGrpCat.{max u w}]
    [CountableAB4 AddCommGrpCat.{max u w}]
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [∀ n, Injective (I.X n)],
    QuasiIso
      (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map
        ((fiberSectionsColumnsFunctor F J).obj I)
        (fiberSectionsBicomplexCoaugmentation F J I)
        (fiberSectionsBicomplexCoaugmentation_comp_d F J I)))

end CategoryTheory.Grothendieck
