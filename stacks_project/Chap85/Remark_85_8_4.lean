/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.UnboundedCohomology
public import ReasLib.CategoryTheory.Sites.Grothendieck.UnboundedCohomology

/-!
# Remark 85.8.4

The unbounded spectral sequences on total simplicial sites arise from the product-tail
filtration of the stage-sections bicomplex. No convergence or abutment is asserted.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape DerivedCategory Opposite Functor
open FilteredComplex RightDerived.Cochain AlgebraicTopology

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
variable [HasCountableProducts AddCommGrpCat.{max u w}]

variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [(globalSectionsTotalFunctor C J).Additive]
variable [∀ n : ℕ,
    (Functor.RightDerived.Cochain.toDerived (sectionsStageGamma C J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]
variable [(Functor.RightDerived.Cochain.toDerived (globalSectionsTotalFunctor C J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]


#check (CategoryTheory.SimplicialSites.rGammaIsoProductTotal C J :
    ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K),
    IsIsomorphic ((unboundedRGammaFunctor C J).obj K)
      (DerivedCategory.Q.obj (HomologicalComplex₂.ProductTotal.complex (sectionsBicomplex C J I))))

/- Remark 85.8.4 -/
@[stacks 0H0V] #check (CategoryTheory.SimplicialSites.unboundedExists_spectralSequence C J :
    ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K),
    ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (hE : IsAssociated (HomologicalComplex₂.ProductTotal.filtration (sectionsBicomplex C J I)) E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅ (unboundedPageOneFunctor C J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (unboundedPageOneDifferential C J p q).app K =
          (E.page 1).d (p, q) (p + 1, q) ≫ (pageOneIso (p + 1) q).hom)

#check (CategoryTheory.SimplicialSites.unboundedSpectralSequence_functorial C J :
    ∃ (E : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
        CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (A : ∀ I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ,
        Association (HomologicalComplex₂.ProductTotal.filtration (sectionsBicomplex C J I))
          (E.obj I))
      (pageOneIso : ∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
        [I.IsKInjective] [∀ n, Injective (I.X n)]
        (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
        (hK : DerivedCategory.Q.obj I ≅ K) (p q : ℤ),
        ((E.obj I).page 1).X (p, q) ≅ (unboundedPageOneFunctor C J p q).obj K),
      (∀ {I I' : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ} (fI : I ⟶ I'),
        Page.Zero.IsCompatible (A I).toComparison (A I').toComparison
          (HomologicalComplex₂.ProductTotal.filtrationMap ((sectionsBicomplexFunctor C J).map fI))
          (E.map fI)) ∧
      (∀ (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
        [I.IsKInjective] [∀ n, Injective (I.X n)]
        (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
        (hK : DerivedCategory.Q.obj I ≅ K) (p q : ℤ),
        (pageOneIso I K hK p q).hom ≫ (unboundedPageOneDifferential C J p q).app K =
          ((E.obj I).page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso I K hK (p + 1) q).hom) ∧
      ∀ {I I' : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ}
        [I.IsKInjective] [I'.IsKInjective]
        [∀ n, Injective (I.X n)] [∀ n, Injective (I'.X n)]
        {K L : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})}
        (hK : DerivedCategory.Q.obj I ≅ K) (hL : DerivedCategory.Q.obj I' ≅ L)
        (fI : I ⟶ I') (p q : ℤ),
        ((E.map fI).hom 1).f (p, q) ≫ (pageOneIso I' L hL p q).hom =
          (pageOneIso I K hK p q).hom ≫
            (unboundedPageOneFunctor C J p q).map
              (hK.inv ≫ DerivedCategory.Q.map fI ≫ hL.hom))

end CategoryTheory.SimplicialSites

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
variable [HasCountableProducts AddCommGrpCat.{max u w}]

variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [∀ n : ℕ,
    (Functor.RightDerived.Cochain.toDerived (fiberSectionsStageGamma F J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]
variable [(Functor.RightDerived.Cochain.toDerived (fiberSectionsTotalFunctor F J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]


#check (CategoryTheory.Grothendieck.fiberRGammaIsoProductTotal F J :
    ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K),
    IsIsomorphic ((fiberUnboundedRGammaFunctor F J).obj K)
      (DerivedCategory.Q.obj (HomologicalComplex₂.ProductTotal.complex (fiberSectionsBicomplex F J I))))

#check (CategoryTheory.Grothendieck.fiberExists_spectralSequence F J :
    ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K),
    ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (hE : IsAssociated (HomologicalComplex₂.ProductTotal.filtration (fiberSectionsBicomplex F J I)) E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅ (fiberUnboundedPageOneFunctor F J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (fiberUnboundedPageOneDifferential F J p q).app K =
          (E.page 1).d (p, q) (p + 1, q) ≫ (pageOneIso (p + 1) q).hom)

#check (CategoryTheory.Grothendieck.fiberSpectralSequence_functorial F J :
    ∃ (E : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
        CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (A : ∀ I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ,
        Association (HomologicalComplex₂.ProductTotal.filtration (fiberSectionsBicomplex F J I))
          (E.obj I))
      (pageOneIso : ∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
        [I.IsKInjective] [∀ n, Injective (I.X n)]
        (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
        (hK : DerivedCategory.Q.obj I ≅ K) (p q : ℤ),
        ((E.obj I).page 1).X (p, q) ≅ (fiberUnboundedPageOneFunctor F J p q).obj K),
      (∀ {I I' : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ} (fI : I ⟶ I'),
        Page.Zero.IsCompatible (A I).toComparison (A I').toComparison
          (HomologicalComplex₂.ProductTotal.filtrationMap ((fiberSectionsBicomplexFunctor F J).map fI))
          (E.map fI)) ∧
      (∀ (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
        [I.IsKInjective] [∀ n, Injective (I.X n)]
        (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
        (hK : DerivedCategory.Q.obj I ≅ K) (p q : ℤ),
        (pageOneIso I K hK p q).hom ≫ (fiberUnboundedPageOneDifferential F J p q).app K =
          ((E.obj I).page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso I K hK (p + 1) q).hom) ∧
      ∀ {I I' : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ}
        [I.IsKInjective] [I'.IsKInjective]
        [∀ n, Injective (I.X n)] [∀ n, Injective (I'.X n)]
        {K L : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})}
        (hK : DerivedCategory.Q.obj I ≅ K) (hL : DerivedCategory.Q.obj I' ≅ L)
        (fI : I ⟶ I') (p q : ℤ),
        ((E.map fI).hom 1).f (p, q) ≫ (pageOneIso I' L hL p q).hom =
          (pageOneIso I K hK p q).hom ≫
            (fiberUnboundedPageOneFunctor F J p q).map
              (hK.inv ≫ DerivedCategory.Q.map fI ≫ hL.hom))

end CategoryTheory.Grothendieck

