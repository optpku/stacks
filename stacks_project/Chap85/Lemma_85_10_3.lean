/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import stacks_project.Chap85.Lemma_85_10_3_Cohomology
public import stacks_project.Chap85.Lemma_85_10_3_Fiberwise

/-!
# Lemma 85.10.3

In Situation 85.3.3 let `O` be a sheaf of rings. For `K` in `D⁺(O)` there is a
spectral sequence `(E_r, d_r)_{r ≥ 0}` with `E₁^{p,q} = H^q(C_p, K_p)` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}` converging to `H^{p+q}(C_total, K)`. This
spectral sequence is functorial in `K`.
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
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable [∀ p : ℕ,
    (componentSectionsFunctor C J O p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(totalSectionsFunctor C J O).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]

/-- Lemma 85.10.3 (1): in Situation 85.3.3 case A, for `K` in `D⁺(O)` there is a
spectral sequence `(E_r, d_r)_{r ≥ 0}` with `E₁^{p,q} = H^q(C_p, K_p)` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}` converging to `H^{p+q}(C_total, K)`. -/
@[stacks 0D7E]
theorem exists_spectralSequence
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    ∃ (S : WithAbutment (fun n ↦ totalHypercohomologyFunctor C J O n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅ (modulePageOneFunctor C J O p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (modulePageOneDifferential C J O p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- Lemma 85.10.3 (2): in Situation 85.3.3 case A, the spectral sequence of
`exists_spectralSequence` is functorial in `K`. -/
@[stacks 0D7E]
theorem spectralSequence_functorial
    {K L : DerivedCategory.Plus (SheafOfModules.{w} O)}
    (f : K ⟶ L) :
    ∃ (SK : WithAbutment (fun n ↦ totalHypercohomologyFunctor C J O n) K)
      (SL : WithAbutment (fun n ↦ totalHypercohomologyFunctor C J O n) L)
      (pageOneIsoK : ∀ p q : ℤ,
        (SK.sequence.page 1).X (p, q) ≅ (modulePageOneFunctor C J O p q).obj K)
      (pageOneIsoL : ∀ p q : ℤ,
        (SL.sequence.page 1).X (p, q) ≅ (modulePageOneFunctor C J O p q).obj L)
      (φ : WithAbutment.Map (fun n ↦ totalHypercohomologyFunctor C J O n) f SK SL),
      (∀ p q : ℤ,
        (pageOneIsoK p q).hom ≫ (modulePageOneDifferential C J O p q).app K =
          (SK.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoK (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoL p q).hom ≫ (modulePageOneDifferential C J O p q).app L =
          (SL.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoL (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.sequenceMap.hom 1).f (p, q)) ≫ (pageOneIsoL p q).hom =
          (pageOneIsoK p q).hom ≫ (modulePageOneFunctor C J O p q).map f :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable [∀ p : ℕ,
    (fiberComponentSectionsFunctor F J O p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(fiberTotalSectionsFunctor F J O).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]

/-- Lemma 85.10.3 (3): in Situation 85.3.3 case B, for `K` in `D⁺(O)` there is a
spectral sequence `(E_r, d_r)_{r ≥ 0}` with `E₁^{p,q} = H^q(C_p, K_p)` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}` converging to `H^{p+q}(C_total, K)`. -/
@[stacks 0D7E]
theorem exists_spectralSequence
    (K : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    ∃ (S : WithAbutment (fun n ↦ fiberTotalHypercohomologyFunctor F J O n) K)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J O p q).obj K),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (fiberPageOneDifferential F J O p q).app K =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- Lemma 85.10.3 (4): in Situation 85.3.3 case B, the spectral sequence of
`exists_spectralSequence` is functorial in `K`. -/
@[stacks 0D7E]
theorem spectralSequence_functorial
    {K L : DerivedCategory.Plus (SheafOfModules.{w} O)}
    (f : K ⟶ L) :
    ∃ (SK : WithAbutment (fun n ↦ fiberTotalHypercohomologyFunctor F J O n) K)
      (SL : WithAbutment (fun n ↦ fiberTotalHypercohomologyFunctor F J O n) L)
      (pageOneIsoK : ∀ p q : ℤ,
        (SK.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J O p q).obj K)
      (pageOneIsoL : ∀ p q : ℤ,
        (SL.sequence.page 1).X (p, q) ≅
          (fiberPageOneFunctor F J O p q).obj L)
      (φ : WithAbutment.Map (fun n ↦ fiberTotalHypercohomologyFunctor F J O n) f SK SL),
      (∀ p q : ℤ,
        (pageOneIsoK p q).hom ≫ (fiberPageOneDifferential F J O p q).app K =
          (SK.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoK (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoL p q).hom ≫ (fiberPageOneDifferential F J O p q).app L =
          (SL.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoL (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.sequenceMap.hom 1).f (p, q)) ≫ (pageOneIsoL p q).hom =
          (pageOneIsoK p q).hom ≫ (fiberPageOneFunctor F J O p q).map f :=
  sorry

end CategoryTheory.Grothendieck
