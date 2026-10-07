module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import stacks_project.Chap85.Lemma_85_8_3_Bicomplex
public import stacks_project.Chap85.Lemma_85_8_3_Fiberwise

/-!
# Lemma 85.8.3

In Situation 85.3.3, for `K` in `D⁺(C_total)` there is a cohomological spectral
sequence `(E_r, d_r)_{r ≥ 0}` with `E₁^{p,q} = H^q(C_p, K_p)` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`, converging to `H^{p+q}(C_total, K)`.
The spectral sequence is functorial in `K`.
-/

@[expose] public section

open CategoryTheory HomologicalComplex ComplexShape DerivedCategory Opposite
open FilteredComplex.SpectralSequence.Realization

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
variable [∀ n : ℕ,
    (sectionsStageGamma C J n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]
variable [(globalSectionsTotalFunctor C J).Additive]
variable [(globalSectionsTotalFunctor C J).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]

/-- Lemma 85.8.3 (1): in Situation 85.3.3 case A, for `K` in `D⁺(C_total)` there is a
cohomological spectral sequence `(E_r)_{r ≥ 0}` with `E₁^{p,q} = H^q(C_p, K_p)` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`, converging to `H^{p+q}(C_total, K)`. -/
@[stacks 09WJ]
theorem exists_spectralSequence
    (K : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})) :
    ∃ (S : WithAbutment (fun n ↦ abutmentFunctor C J n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅ (pageOneFunctor C J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (pageOneDifferential C J p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- Lemma 85.8.3 (2): in Situation 85.3.3 case A, the spectral sequence of
`exists_spectralSequence` is functorial in `K`. -/
@[stacks 09WJ]
theorem spectralSequence_functorial
    {K L : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})}
    (f : K ⟶ L) :
    ∃ (SK : WithAbutment (fun n ↦ abutmentFunctor C J n) K)
      (SL : WithAbutment (fun n ↦ abutmentFunctor C J n) L)
      (pageOneIsoK : ∀ p q : ℤ,
        (SK.sequence.page 1).X (p, q) ≅ (pageOneFunctor C J p q).obj K)
      (pageOneIsoL : ∀ p q : ℤ,
        (SL.sequence.page 1).X (p, q) ≅ (pageOneFunctor C J p q).obj L)
      (φ : WithAbutment.Map (fun n ↦ abutmentFunctor C J n) f SK SL),
      (∀ p q : ℤ,
        (pageOneIsoK p q).hom ≫ (pageOneDifferential C J p q).app K =
          (SK.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoK (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoL p q).hom ≫ (pageOneDifferential C J p q).app L =
          (SL.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoL (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.sequenceMap.hom 1).f (p, q)) ≫ (pageOneIsoL p q).hom =
          (pageOneIsoK p q).hom ≫ (pageOneFunctor C J p q).map f :=
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
variable [∀ n : ℕ,
    (fiberSectionsStageGamma F J n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]
variable [(fiberSectionsTotalFunctor F J).Additive]
variable [(fiberSectionsTotalFunctor F J).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]

/-- Lemma 85.8.3 (3): in Situation 85.3.3 case B, for `K` in `D⁺(C_total)` there is a
cohomological spectral sequence `(E_r)_{r ≥ 0}` with `E₁^{p,q} = H^q(C_p, K_p)` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`, converging to `H^{p+q}(C_total, K)`. -/
@[stacks 09WJ]
theorem exists_spectralSequence
    (K : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})) :
    ∃ (S : WithAbutment (fun n ↦ fiberAbutmentFunctor F J n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (fiberPageOneDifferential F J p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- Lemma 85.8.3 (4): in Situation 85.3.3 case B, the spectral sequence of
`exists_spectralSequence` is functorial in `K`. -/
@[stacks 09WJ]
theorem spectralSequence_functorial
    {K L : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})}
    (f : K ⟶ L) :
    ∃ (SK : WithAbutment (fun n ↦ fiberAbutmentFunctor F J n) K)
      (SL : WithAbutment (fun n ↦ fiberAbutmentFunctor F J n) L)
      (pageOneIsoK : ∀ p q : ℤ,
        (SK.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J p q).obj K)
      (pageOneIsoL : ∀ p q : ℤ,
        (SL.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J p q).obj L)
      (φ : WithAbutment.Map (fun n ↦ fiberAbutmentFunctor F J n) f SK SL),
      (∀ p q : ℤ,
        (pageOneIsoK p q).hom ≫ (fiberPageOneDifferential F J p q).app K =
          (SK.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoK (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoL p q).hom ≫ (fiberPageOneDifferential F J p q).app L =
          (SL.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoL (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.sequenceMap.hom 1).f (p, q)) ≫ (pageOneIsoL p q).hom =
          (pageOneIsoK p q).hom ≫ (fiberPageOneFunctor F J p q).map f :=
  sorry

end CategoryTheory.Grothendieck
