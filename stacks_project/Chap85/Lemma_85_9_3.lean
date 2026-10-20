/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import stacks_project.Chap85.Lemma_85_9_3_Bicomplex
public import stacks_project.Chap85.Lemma_85_9_3_Fiberwise

/-!
# Lemma 85.9.3

In Situation 85.3.3 let `a0` be an augmentation towards a site `D` as in
Remark 85.4.1. For any `K` in `D⁺(C_total)` there is a spectral sequence
`(E_r, d_r)_{r ≥ 0}` with `E₁^{p,q} = R^q a_{p,*} K_p` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`, converging to `R^{p+q} a_* K`.
This spectral sequence is functorial in `K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape DerivedCategory Opposite
open FilteredComplex.SpectralSequence.Realization
open scoped Simplicial

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
variable [∀ n : ℕ,
    (augmentationStageGamma C J K u0 n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]
variable [(IsAugmentation.abelianPushforward C J K u0).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}))]
include h_morphism
include h_aug

/-- Lemma 85.9.3 (1): in Situation 85.3.3 case A, with an augmentation towards a
site `D` as in Remark 85.4.1, for `K` in `D⁺(C_total)` there is a cohomological
spectral sequence `(E_r)_{r ≥ 0}` with `E₁^{p,q} = R^q a_{p,*} K_p` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`, converging to `R^{p+q} a_* K`. -/
@[stacks 0D7A]
theorem exists_augmentationSpectralSequence
    (X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})) :
    ∃ (S : WithAbutment (fun n ↦ augmentationAbutmentFunctor C J K u0 n) X)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (augmentationPageOneFunctor C J K u0 p q).obj X),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (augmentationPageOneDifferential C J K u0 p q).app X =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- Lemma 85.9.3 (2): in Situation 85.3.3 case A, the spectral sequence of
`exists_augmentationSpectralSequence` is functorial in `K`. -/
@[stacks 0D7A]
theorem augmentationSpectralSequence_functorial
    {X Y : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{w})}
    (f : X ⟶ Y) :
    ∃ (SX : WithAbutment (fun n ↦ augmentationAbutmentFunctor C J K u0 n) X)
      (SY : WithAbutment (fun n ↦ augmentationAbutmentFunctor C J K u0 n) Y)
      (pageOneIsoX : ∀ p q : ℤ,
        (SX.sequence.page 1).X (p, q) ≅
          (augmentationPageOneFunctor C J K u0 p q).obj X)
      (pageOneIsoY : ∀ p q : ℤ,
        (SY.sequence.page 1).X (p, q) ≅
          (augmentationPageOneFunctor C J K u0 p q).obj Y)
      (φ : WithAbutment.Map (fun n ↦ augmentationAbutmentFunctor C J K u0 n) f SX SY),
      (∀ p q : ℤ,
        (pageOneIsoX p q).hom ≫ (augmentationPageOneDifferential C J K u0 p q).app X =
          (SX.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoX (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoY p q).hom ≫ (augmentationPageOneDifferential C J K u0 p q).app Y =
          (SY.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoY (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.sequenceMap.hom 1).f (p, q)) ≫ (pageOneIsoY p q).hom =
          (pageOneIsoX p q).hom ≫ (augmentationPageOneFunctor C J K u0 p q).map f :=
  sorry

end CategoryTheory.SimplicialSites

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
variable [∀ n : ℕ,
    (fiberAugmentationStageGamma F J K u0 n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]
variable [(IsAugmentation.abelianPushforward F J K u0).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}))]

/-- Lemma 85.9.3 (3): in Situation 85.3.3 case B, with an augmentation towards a
site `D` as in Remark 85.4.1, for `K` in `D⁺(C_total)` there is a cohomological
spectral sequence `(E_r)_{r ≥ 0}` with `E₁^{p,q} = R^q a_{p,*} K_p` and
`d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`, converging to `R^{p+q} a_* K`. -/
@[stacks 0D7A]
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

/-- Lemma 85.9.3 (4): in Situation 85.3.3 case B, the spectral sequence of
`exists_fiberAugmentationSpectralSequence` is functorial in `K`. -/
@[stacks 0D7A]
theorem fiberAugmentationSpectralSequence_functorial
    {X Y : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{w})}
    (f : X ⟶ Y) :
    ∃ (SX : WithAbutment (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) X)
      (SY : WithAbutment (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) Y)
      (pageOneIsoX : ∀ p q : ℤ,
        (SX.sequence.page 1).X (p, q) ≅
          (fiberAugmentationPageOneFunctor F J K u0 p q).obj X)
      (pageOneIsoY : ∀ p q : ℤ,
        (SY.sequence.page 1).X (p, q) ≅
          (fiberAugmentationPageOneFunctor F J K u0 p q).obj Y)
      (φ : WithAbutment.Map
        (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) f SX SY),
      (∀ p q : ℤ,
        (pageOneIsoX p q).hom ≫
            (fiberAugmentationPageOneDifferential F J K u0 p q).app X =
          (SX.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoX (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoY p q).hom ≫
            (fiberAugmentationPageOneDifferential F J K u0 p q).app Y =
          (SY.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoY (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.sequenceMap.hom 1).f (p, q)) ≫ (pageOneIsoY p q).hom =
          (pageOneIsoX p q).hom ≫
            (fiberAugmentationPageOneFunctor F J K u0 p q).map f :=
  sorry

end CategoryTheory.Grothendieck
