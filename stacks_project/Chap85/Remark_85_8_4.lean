/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Association
public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.AssociationMorphism
public import stacks_project.Chap85.Remark_85_8_4_Fiberwise
public import stacks_project.Chap85.Remark_85_8_4_ProductTotal

/-!
# Remark 85.8.4

In Situation 85.3.3, dropping the bounded-below hypothesis of Lemma 85.8.3, a
K-injective complex `I^•` of injective sheaves representing `K` in `D(C_total)`
identifies `RΓ(C_total, K)` with the product total `Tot_π(A)` of
`A^{p,q} = Γ(C_p, I^q_p)`. The product-tail filtration of `Tot_π(A)` yields a
cohomological spectral sequence associated in the sense of Homology 12.25,
except for regularity, boundedness, convergence, and abutment, with
`E₁^{p,q} = H^q(C_p, K_p)`. The sequence is natural in maps of such
representatives. Cases A and B of Situation 85.3.3.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape DerivedCategory Opposite Functor
open FilteredComplex
open RightDerived.Cochain

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
    (toDerived (sectionsStageGamma C J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]
variable [(toDerived (globalSectionsTotalFunctor C J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))]

/-- Remark 85.8.4 (1): in Situation 85.3.3 case A, if `I` is a K-injective complex of
injective sheaves representing `K`, then `RΓ(C_total, K)` identifies with
`Q(Tot_π(A))`, where `A^{p,q} = Γ(C_p, I^q_p)` and `Tot_π` is
`HomologicalComplex₂.ProductTotal.complex`. The identification expands the chain
`RΓ = RHom(ℤ, K) = RHom(complex C J, K) = Γ(Hom^•(complex, I)) = Tot_π(A)`. -/
@[stacks 0H0V]
theorem rGammaIsoProductTotal
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K) :
    IsIsomorphic ((unboundedRGammaFunctor C J).obj K)
      (DerivedCategory.Q.obj (sectionsProductTotal C J I)) :=
  sorry

/-- Remark 85.8.4 (2): in Situation 85.3.3 case A, the product-tail filtration of
`Tot_π(A)` yields an associated cohomological spectral sequence with
`E₁^{p,q} = H^q(C_p, K_p)`, without regularity, boundedness, convergence, or
abutment. -/
@[stacks 0H0V]
theorem exists_spectralSequence
    (I : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K) :
    ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (hE : IsAssociated (sectionsProductFiltration C J I) E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅ (unboundedPageOneFunctor C J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (unboundedPageOneDifferential C J p q).app K =
          (E.page 1).d (p, q) (p + 1, q) ≫ (pageOneIso (p + 1) q).hom :=
  sorry

/-- Remark 85.8.4 (3): in Situation 85.3.3 case A, a map of K-injective injective-term
representatives compatible with a map of derived objects induces a map of the
associated spectral sequences, commuting with the first-page identifications. -/
@[stacks 0H0V]
theorem spectralSequence_functorial
    {I I' : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [∀ n, Injective (I.X n)] [∀ n, Injective (I'.X n)]
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I)]
    [HomologicalComplex₂.ProductTotal.HasTotal (sectionsBicomplex C J I')]
    {K L : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})}
    (hK : DerivedCategory.Q.obj I ≅ K) (hL : DerivedCategory.Q.obj I' ≅ L)
    (fI : I ⟶ I') (f : K ⟶ L)
    (hf : hK.inv ≫ DerivedCategory.Q.map fI ≫ hL.hom = f) :
    ∃ (EK : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (EL : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (AK : Association (sectionsProductFiltration C J I) EK)
      (AL : Association (sectionsProductFiltration C J I') EL)
      (pageOneIsoK : ∀ p q : ℤ,
        (EK.page 1).X (p, q) ≅ (unboundedPageOneFunctor C J p q).obj K)
      (pageOneIsoL : ∀ p q : ℤ,
        (EL.page 1).X (p, q) ≅ (unboundedPageOneFunctor C J p q).obj L)
      (α : sectionsProductFiltration C J I ⟶ sectionsProductFiltration C J I')
      (φ : Association.Hom AK AL α),
      (∀ p q : ℤ,
        (pageOneIsoK p q).hom ≫ (unboundedPageOneDifferential C J p q).app K =
          (EK.page 1).d (p, q) (p + 1, q) ≫ (pageOneIsoK (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoL p q).hom ≫ (unboundedPageOneDifferential C J p q).app L =
          (EL.page 1).d (p, q) (p + 1, q) ≫ (pageOneIsoL (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.hom.hom 1).f (p, q)) ≫ (pageOneIsoL p q).hom =
          (pageOneIsoK p q).hom ≫ (unboundedPageOneFunctor C J p q).map f :=
  sorry

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
    (toDerived (fiberSectionsStageGamma F J n)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]
variable [(toDerived (fiberSectionsTotalFunctor F J)).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))]

/-- Remark 85.8.4 (4): in Situation 85.3.3 case B, if `I` is a K-injective complex of
injective sheaves representing `K`, then `RΓ(C_total, K)` identifies with
`Q(Tot_π(A))`. -/
@[stacks 0H0V]
theorem fiberRGammaIsoProductTotal
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K) :
    IsIsomorphic ((fiberUnboundedRGammaFunctor F J).obj K)
      (DerivedCategory.Q.obj (fiberSectionsProductTotal F J I)) :=
  sorry

/-- Remark 85.8.4 (5): in Situation 85.3.3 case B, the product-tail filtration of
`Tot_π(A)` yields an associated cohomological spectral sequence with
`E₁^{p,q} = H^q(C_p, K_p)`, without regularity, boundedness, convergence, or
abutment. -/
@[stacks 0H0V]
theorem fiberExists_spectralSequence
    (I : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] [∀ n, Injective (I.X n)]
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    (hK : DerivedCategory.Q.obj I ≅ K) :
    ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (hE : IsAssociated (fiberSectionsProductFiltration F J I) E)
      (pageOneIso : ∀ p q : ℤ,
        (E.page 1).X (p, q) ≅ (fiberUnboundedPageOneFunctor F J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (fiberUnboundedPageOneDifferential F J p q).app K =
          (E.page 1).d (p, q) (p + 1, q) ≫ (pageOneIso (p + 1) q).hom :=
  sorry

/-- Remark 85.8.4 (6): in Situation 85.3.3 case B, a map of K-injective injective-term
representatives compatible with a map of derived objects induces a map of the
associated spectral sequences, commuting with the first-page identifications. -/
@[stacks 0H0V]
theorem fiberSpectralSequence_functorial
    {I I' : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [∀ n, Injective (I.X n)] [∀ n, Injective (I'.X n)]
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I)]
    [HomologicalComplex₂.ProductTotal.HasTotal (fiberSectionsBicomplex F J I')]
    {K L : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})}
    (hK : DerivedCategory.Q.obj I ≅ K) (hL : DerivedCategory.Q.obj I' ≅ L)
    (fI : I ⟶ I') (f : K ⟶ L)
    (hf : hK.inv ≫ DerivedCategory.Q.map fI ≫ hL.hom = f) :
    ∃ (EK : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (EL : CohomologicalSpectralSequence AddCommGrpCat.{max u w} 0)
      (AK : Association (fiberSectionsProductFiltration F J I) EK)
      (AL : Association (fiberSectionsProductFiltration F J I') EL)
      (pageOneIsoK : ∀ p q : ℤ,
        (EK.page 1).X (p, q) ≅ (fiberUnboundedPageOneFunctor F J p q).obj K)
      (pageOneIsoL : ∀ p q : ℤ,
        (EL.page 1).X (p, q) ≅ (fiberUnboundedPageOneFunctor F J p q).obj L)
      (α : fiberSectionsProductFiltration F J I ⟶ fiberSectionsProductFiltration F J I')
      (φ : Association.Hom AK AL α),
      (∀ p q : ℤ,
        (pageOneIsoK p q).hom ≫ (fiberUnboundedPageOneDifferential F J p q).app K =
          (EK.page 1).d (p, q) (p + 1, q) ≫ (pageOneIsoK (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoL p q).hom ≫ (fiberUnboundedPageOneDifferential F J p q).app L =
          (EL.page 1).d (p, q) (p + 1, q) ≫ (pageOneIsoL (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.hom.hom 1).f (p, q)) ≫ (pageOneIsoL p q).hom =
          (pageOneIsoK p q).hom ≫ (fiberUnboundedPageOneFunctor F J p q).map f :=
  sorry

end CategoryTheory.Grothendieck
