/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import stacks_project.Chap85.Lemma_85_11_4_Bicomplex
public import stacks_project.Chap85.Lemma_85_11_4_Fiberwise

/-!
# Lemma 85.11.4

In Situation 85.3.3, with an augmentation towards a site `D` as in
Remark 85.4.1 and a ring map `O_D ⟶ a_* O`, for any `K` in `D⁺(O)` there is a
spectral sequence `(E_r, d_r)_{r ≥ 0}` in `Mod(O_D)` with
`E₁^{p,q} = R^q a_{p,*} K_p`, converging to `R^{p+q} a_* K`. This spectral
sequence is functorial in `K`.
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
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos C J K u0).ringDirectImage.obj O)
variable [(SheafOfModules.restrictScalars.{w}
    (moduleAugmentationHom C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp
      (moduleAugmentationHom C J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
variable [∀ n : ℕ,
    (moduleAugmentationStageGamma C J K u0 O O_D aSharp n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(moduleAugmentationHom C J K u0 O O_D aSharp).modulePushforward.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
include h_morphism
include h_aug

/-- Lemma 85.11.4 (1): in Situation 85.3.3 case A, with an augmentation towards a
site `D` as in Remark 85.4.1 and a ring map `O_D ⟶ a_* O`, for `K` in `D⁺(O)`
there is a cohomological spectral sequence `(E_r)_{r ≥ 0}` in `Mod(O_D)` with
`E₁^{p,q} = R^q a_{p,*} K_p` and `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`,
converging to `R^{p+q} a_* K`. -/
@[stacks 0D7F]
theorem exists_moduleAugmentationSpectralSequence
    (X : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    ∃ (S : WithAbutment (fun n ↦ moduleAugmentationAbutmentFunctor C J K u0 O O_D aSharp n) X)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q).obj X),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫
            (moduleAugmentationPageOneDifferential C J K u0 O O_D aSharp p q).app X =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- Lemma 85.11.4 (2): in Situation 85.3.3 case A, the spectral sequence of
`exists_moduleAugmentationSpectralSequence` is functorial in `K`. -/
@[stacks 0D7F]
theorem moduleAugmentationSpectralSequence_functorial
    {X Y : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : X ⟶ Y) :
    ∃ (SX : WithAbutment (fun n ↦ moduleAugmentationAbutmentFunctor C J K u0 O O_D aSharp n) X)
      (SY : WithAbutment (fun n ↦ moduleAugmentationAbutmentFunctor C J K u0 O O_D aSharp n) Y)
      (pageOneIsoX : ∀ p q : ℤ,
        (SX.sequence.page 1).X (p, q) ≅
          (moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q).obj X)
      (pageOneIsoY : ∀ p q : ℤ,
        (SY.sequence.page 1).X (p, q) ≅
          (moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q).obj Y)
      (φ : WithAbutment.Map
        (fun n ↦ moduleAugmentationAbutmentFunctor C J K u0 O O_D aSharp n) f SX SY),
      (∀ p q : ℤ,
        (pageOneIsoX p q).hom ≫
            (moduleAugmentationPageOneDifferential C J K u0 O O_D aSharp p q).app X =
          (SX.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoX (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoY p q).hom ≫
            (moduleAugmentationPageOneDifferential C J K u0 O O_D aSharp p q).app Y =
          (SY.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoY (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.sequenceMap.hom 1).f (p, q)) ≫ (pageOneIsoY p q).hom =
          (pageOneIsoX p q).hom ≫
            (moduleAugmentationPageOneFunctor C J K u0 O O_D aSharp p q).map f :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos F J K u0).ringDirectImage.obj O)
variable [(SheafOfModules.restrictScalars.{w}
    (fiberModuleAugmentationHom F J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((fiberStageMorphism F J O n).comp
      (fiberModuleAugmentationHom F J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
variable [∀ n : ℕ,
    (fiberModuleAugmentationStageGamma F J K u0 O O_D aSharp n).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]
variable [(fiberModuleAugmentationHom F J K u0 O O_D aSharp).modulePushforward.toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{w} O))]

/-- Lemma 85.11.4 (3): in Situation 85.3.3 case B, with an augmentation towards a
site `D` as in Remark 85.4.1 and a ring map `O_D ⟶ a_* O`, for `K` in `D⁺(O)`
there is a cohomological spectral sequence `(E_r)_{r ≥ 0}` in `Mod(O_D)` with
`E₁^{p,q} = R^q a_{p,*} K_p` and `d₁^{p,q} : E₁^{p,q} ⟶ E₁^{p+1,q}`,
converging to `R^{p+q} a_* K`. -/
@[stacks 0D7F]
theorem exists_fiberModuleAugmentationSpectralSequence
    (X : DerivedCategory.Plus (SheafOfModules.{w} O)) :
    ∃ (S : WithAbutment
        (fun n ↦ fiberModuleAugmentationAbutmentFunctor F J K u0 O O_D aSharp n) X)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).obj X),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫
            (fiberModuleAugmentationPageOneDifferential F J K u0 O O_D aSharp p q).app X =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom :=
  sorry

/-- Lemma 85.11.4 (4): in Situation 85.3.3 case B, the spectral sequence of
`exists_fiberModuleAugmentationSpectralSequence` is functorial in `K`. -/
@[stacks 0D7F]
theorem fiberModuleAugmentationSpectralSequence_functorial
    {X Y : DerivedCategory.Plus (SheafOfModules.{w} O)} (f : X ⟶ Y) :
    ∃ (SX : WithAbutment
        (fun n ↦ fiberModuleAugmentationAbutmentFunctor F J K u0 O O_D aSharp n) X)
      (SY : WithAbutment
        (fun n ↦ fiberModuleAugmentationAbutmentFunctor F J K u0 O O_D aSharp n) Y)
      (pageOneIsoX : ∀ p q : ℤ,
        (SX.sequence.page 1).X (p, q) ≅
          (fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).obj X)
      (pageOneIsoY : ∀ p q : ℤ,
        (SY.sequence.page 1).X (p, q) ≅
          (fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).obj Y)
      (φ : WithAbutment.Map
        (fun n ↦ fiberModuleAugmentationAbutmentFunctor F J K u0 O O_D aSharp n) f SX SY),
      (∀ p q : ℤ,
        (pageOneIsoX p q).hom ≫
            (fiberModuleAugmentationPageOneDifferential F J K u0 O O_D aSharp p q).app X =
          (SX.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoX (p + 1) q).hom) ∧
      (∀ p q : ℤ,
        (pageOneIsoY p q).hom ≫
            (fiberModuleAugmentationPageOneDifferential F J K u0 O O_D aSharp p q).app Y =
          (SY.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIsoY (p + 1) q).hom) ∧
      ∀ p q : ℤ,
        ((φ.sequenceMap.hom 1).f (p, q)) ≫ (pageOneIsoY p q).hom =
          (pageOneIsoX p q).hom ≫
            (fiberModuleAugmentationPageOneFunctor F J K u0 O O_D aSharp p q).map f :=
  sorry

end CategoryTheory.Grothendieck
