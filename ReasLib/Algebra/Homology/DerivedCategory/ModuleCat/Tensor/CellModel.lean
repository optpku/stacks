/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CellReplacement
public import ReasLib.Algebra.Category.ModuleCat.Graded.Colimits
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Monoidal
public import Mathlib.CategoryTheory.Localization.Prod

/-! # A cell model for the two-variable derived tensor product -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open DerivedCategory HomologicalComplex ComplexShape

noncomputable section

universe u

namespace ModuleCat.DerivedTensorCellModel

variable (R : Type u) [CommRing R]

/-- Localize the tensor product of the two specified cell replacements. -/
def cochain :
    CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  (CellReplacement.functor R).prod (CellReplacement.functor R) ⋙
    MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (DerivedCategory.Q (C := ModuleCat.{u} R))

variable {R}

/-- Tensoring the replacement maps of two quasi-isomorphisms gives a quasi-isomorphism. -/
theorem map_quasiIso
    {A A' B B' : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : A ⟶ A') (b : B ⟶ B') (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (HomologicalComplex.tensorHom
      (CellReplacement.replacementMap a) (CellReplacement.replacementMap b)) := sorry

variable (R)

/-- The displayed cochain model inverts componentwise quasi-isomorphisms. -/
theorem cochain_inverts :
    ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ)).prod
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))).IsInvertedBy (cochain R) := by
  intro X Y f hf
  exact (Localization.isoOfHom (DerivedCategory.Q (C := ModuleCat.{u} R))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
    (HomologicalComplex.tensorHom
      (CellReplacement.replacementMap f.1) (CellReplacement.replacementMap f.2))
    (map_quasiIso f.1 f.2 hf.1 hf.2)).isIso_hom

/-- Descend the cell tensor model along localization in both inputs. -/
def derived :
    DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift (cochain R) (cochain_inverts R)
    ((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R)))

/-- The native localization comparison for the cell tensor model. -/
def fac : ((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ derived R ≅ cochain R :=
  Localization.fac (cochain R) (cochain_inverts R)
    ((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R)))

/-- Tensor the two augmentations to obtain the cochain counit. -/
def cochainCounit :
    ((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ derived R ⟶
      MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
  (fac R).hom ≫ Functor.whiskerRight
    ((CellReplacement.augmentationNatTrans R).prod
      (CellReplacement.augmentationNatTrans R))
    (MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ (DerivedCategory.Q (C := ModuleCat.{u} R)))

/-- Transport the augmentation counit to a pair of homotopy objects. -/
def homotopyCounitComponent
    (X : HomotopyCategory (ModuleCat.{u} R) (up ℤ) ×
      HomotopyCategory (ModuleCat.{u} R) (up ℤ)) :
    (derived R).obj (((DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R))).obj X) ⟶
      ((DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R))).obj X :=
  (derived R).map (Prod.mkHom
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app X.1.as)
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app X.2.as)) ≫
  (cochainCounit R).app (X.1.as, X.2.as) ≫
  (DerivedTensor.Bifunctor.sourceFunctorObjIso X.1.as X.2.as).inv

/-- The transported augmentation components respect homotopy morphisms in both variables. -/
theorem homotopyCounitComponent_naturality
    {X Y : HomotopyCategory (ModuleCat.{u} R) (up ℤ) ×
      HomotopyCategory (ModuleCat.{u} R) (up ℤ)} (a : X ⟶ Y) :
    ((DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ derived R).map a ≫
        homotopyCounitComponent R Y =
      homotopyCounitComponent R X ≫ ((DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R))).map a := sorry

/-- The natural augmentation from the localized cell model to the homotopy tensor source. -/
def homotopyCounit : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ derived R ⟶
    (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)) where
  app := homotopyCounitComponent R
  naturality := fun _ _ a ↦ homotopyCounitComponent_naturality R a

variable {R}

/-- Formally invert the specified cell augmentation of a cochain complex. -/
def inputAugmentationIso (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    (DerivedCategory.Q (C := ModuleCat.{u} R)).obj (CellReplacement.replacement A) ≅ (DerivedCategory.Q (C := ModuleCat.{u} R)).obj A :=
  Localization.isoOfHom (DerivedCategory.Q (C := ModuleCat.{u} R))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
    (CellReplacement.augmentation A) (CellReplacement.augmentation_quasiIso A)

/-- Evaluate a homotopy comparison on the two cell replacements after reversing their
augmentations, and then use the native cell-model comparison. -/
def extensionLiftOnInput
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ G ⟶ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)))
    (X : CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ) :
    G.obj (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))).obj X) ⟶
      (derived R).obj (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))).obj X) :=
  G.map (Prod.mkHom (inputAugmentationIso X.1).inv (inputAugmentationIso X.2).inv) ≫
  G.map (Prod.mkHom
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app
      (CellReplacement.replacement X.1))
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app
      (CellReplacement.replacement X.2))) ≫
  β.app ((HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj
      (CellReplacement.replacement X.1),
    (HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj
      (CellReplacement.replacement X.2)) ≫
  (DerivedTensor.Bifunctor.sourceFunctorObjIso
    (CellReplacement.replacement X.1) (CellReplacement.replacement X.2)).hom ≫
  (fac R).inv.app X

/-- The specified lift formula is natural on cochain inputs. -/
theorem extensionLiftOnInput_naturality
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ G ⟶ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)))
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ}
    (a : X ⟶ Y) :
    (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ G).map a ≫ extensionLiftOnInput G β Y =
      extensionLiftOnInput G β X ≫
        (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ derived R).map a := sorry

/-- Descend the explicit cochain lift formula to the derived product. -/
def extensionLift
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ G ⟶ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R))) :
    G ⟶ derived R :=
  Localization.liftNatTrans ((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R)))
    ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ)).prod
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ)))
    (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ G)
    (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ derived R) G (derived R)
    { app := extensionLiftOnInput G β
      naturality := fun _ _ a ↦ extensionLiftOnInput_naturality G β a }

/-- The descended lift factors the given homotopy comparison through the augmentation counit. -/
theorem extensionLift_fac
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ G ⟶ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R))) :
    Functor.whiskerLeft (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) (extensionLift G β) ≫
      homotopyCounit R = β := sorry

/-- The specified lift is the unique factorization through the augmentation counit. -/
theorem extensionLift_unique
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ G ⟶ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)))
    (γ : G ⟶ derived R)
    (hγ : Functor.whiskerLeft (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) γ ≫ homotopyCounit R = β) :
    γ = extensionLift G β := sorry

variable (R)

/-- The extension arrow to the cell model uses the displayed lift formula. -/
def terminalExtensionLift
    (E : Functor.RightExtension ((DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)))
      (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R))) :
    E ⟶ Functor.RightExtension.mk (derived R) (homotopyCounit R) :=
  CostructuredArrow.homMk (extensionLift E.left E.hom) (extensionLift_fac E.left E.hom)

/-- The augmentation extension is terminal, with the specified extension arrows. -/
def terminalWitness :
    IsTerminal (Functor.RightExtension.mk (derived R) (homotopyCounit R)) :=
  IsTerminal.ofUniqueHom (terminalExtensionLift R) (by
    intro E m
    apply CostructuredArrow.hom_ext
    exact extensionLift_unique E.left E.hom m.left (by
      have h := m.w
      change Functor.whiskerLeft _ m.left ≫ homotopyCounit R = E.hom ≫ 𝟙 _ at h
      exact h.trans (Category.comp_id _)))

/-- The localized cell model is a left-derived tensor functor with its displayed witness. -/
instance derived_isLeftDerived :
    (derived R).IsLeftDerivedFunctor (homotopyCounit R) (DerivedTensor.Bifunctor.qis (C := ModuleCat.{u} R)) where
  isRightKanExtension := ⟨⟨terminalWitness R⟩⟩

/-- The canonical tensor bifunctor maps to the cell model by the explicit extension lift. -/
def toCellModel : (DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} R)) ⟶ derived R :=
  extensionLift (DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} R)) (DerivedTensor.Bifunctor.counit (C := ModuleCat.{u} R))

/-- The cell model maps to the canonical tensor bifunctor by its native left-derived lift. -/
def fromCellModel : derived R ⟶ (DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} R)) :=
  (DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} R)).leftDerivedLift (DerivedTensor.Bifunctor.counit (C := ModuleCat.{u} R))
    (DerivedTensor.Bifunctor.qis (C := ModuleCat.{u} R)) (derived R) (homotopyCounit R)

/-- The two specified tensor-model comparison transformations are mutual inverses. -/
theorem canonicalIso_laws :
    toCellModel R ≫ fromCellModel R = 𝟙 _ ∧
      fromCellModel R ≫ toCellModel R = 𝟙 _ := sorry

/-- The canonical tensor bifunctor is isomorphic to the displayed cell model. -/
def canonicalIso : (DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} R)) ≅ derived R where
  hom := toCellModel R
  inv := fromCellModel R
  hom_inv_id := (canonicalIso_laws R).1
  inv_hom_id := (canonicalIso_laws R).2

variable {R}

/-- The semi-free cell replacement is K-flat. -/
theorem replacement_isKFlat (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CellReplacement.replacement A).IsKFlat := sorry

/-- Tensoring the two cell augmentations is a quasi-isomorphism when the left input is K-flat. -/
theorem tensorAugmentation_quasiIso (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.IsKFlat) :
    QuasiIso (HomologicalComplex.tensorHom
      (CellReplacement.augmentation P) (CellReplacement.augmentation L)) := sorry

/-- Reverse the localized tensor augmentation and then apply the explicit cell-model comparison. -/
def counitInvOfKFlatLeft (P L : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.IsKFlat) :
    (DerivedCategory.Q (C := ModuleCat.{u} R)).obj (P ⊗ L) ⟶
      DerivedTensor.Bifunctor.obj ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj P) ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj L) :=
  (Localization.isoOfHom (DerivedCategory.Q (C := ModuleCat.{u} R))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
    (HomologicalComplex.tensorHom
      (CellReplacement.augmentation P) (CellReplacement.augmentation L))
    (tensorAugmentation_quasiIso P L hP)).inv ≫
  (fac R).inv.app (P, L) ≫
  (fromCellModel R).app ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj P, (DerivedCategory.Q (C := ModuleCat.{u} R)).obj L)

/-- The canonical tensor counit and the displayed K-flat inverse are mutual inverses. -/
theorem counitIsoOfKFlatLeft_laws (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.IsKFlat) :
    DerivedTensor.Bifunctor.counitAppOfQ P L ≫ counitInvOfKFlatLeft P L hP = 𝟙 _ ∧
      counitInvOfKFlatLeft P L hP ≫ DerivedTensor.Bifunctor.counitAppOfQ P L = 𝟙 _ := sorry

/-- Ordinary tensor with a K-flat left factor computes derived tensor, with its canonical counit. -/
def counitIsoOfKFlatLeft (P L : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.IsKFlat) :
    DerivedTensor.Bifunctor.obj ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj P) ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj L) ≅
      (DerivedCategory.Q (C := ModuleCat.{u} R)).obj (P ⊗ L) where
  hom := DerivedTensor.Bifunctor.counitAppOfQ P L
  inv := counitInvOfKFlatLeft P L hP
  hom_inv_id := (counitIsoOfKFlatLeft_laws P L hP).1
  inv_hom_id := (counitIsoOfKFlatLeft_laws P L hP).2

end ModuleCat.DerivedTensorCellModel
