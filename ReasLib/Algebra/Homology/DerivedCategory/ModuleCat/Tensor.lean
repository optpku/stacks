/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Category.ModuleCat.CellReplacement
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products of modules

@stack 064M

Module categories over commutative rings carry the canonical fixed-left,
fixed-right, and two-variable unbounded derived tensor functors.  This is the
plain-ring instance used by stalk and affine specializations of the generic
derived-tensor API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe w u

namespace ModuleCat

namespace DerivedTensorConstruction

open CategoryTheory.Limits DerivedCategory HomologicalComplex

variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/- The resolution is the displayed semi-free attaching tower, not a selected witness of the
K-flat-resolution existence theorem.  All localizations below use the original `Q` and `Qh`. -/

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

/-- The displayed cell replacement is K-flat. -/
theorem replacement_isKFlat (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CellReplacement.replacement A).IsKFlat := sorry

/-- Tensoring the two augmentations is a quasi-isomorphism when the left input is a cell
replacement. This is the K-flat computation used for the specified splitting below. -/
theorem tensorAugmentation_quasiIso (A B : CochainComplex (ModuleCat.{u} R) ℤ) :
    QuasiIso (HomologicalComplex.tensorHom
      (CellReplacement.augmentation (CellReplacement.replacement A))
      (CellReplacement.augmentation B)) := sorry

/-- The native bifunctor, with its specified augmentation and extension lifts. -/
def model : DerivedTensor.Bifunctor.Model (C := ModuleCat.{u} R) :=
  Functor.LeftDerived.Model.of (derived R) (homotopyCounit R) inferInstance

/-- Fix the right argument of the displayed cell bifunctor. -/
abbrev rightFunctor (E : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (model R).rightFunctor E

/-- The augmentation counit for the fixed-right native functor, with the original
chosen-representative source owner. -/
def rightCounit (E : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory.Qh ⋙ rightFunctor R E ⟶ DerivedTensor.Right.sourceFunctor E :=
  DerivedTensor.Bifunctor.Right.Model.counitOf (model R) E

/-- The fixed-right source on cochain representatives is the ordinary tensor complex. -/
def rightSourceFactors (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ) ⋙
        DerivedTensor.Right.sourceFunctorOfComplex P ≅
      DerivedTensor.Right.complexFunctor P ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.Homotopy.BifunctorTotal.rightFixedFactors
        (curriedTensor (ModuleCat.{u} R)) P) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedTensor.Right.complexFunctor P)
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))

/-- The inverse of the stage leg is the formal localization inverse of the specified tensor
augmentation, followed by the native localization comparison and the input augmentations. -/
def rightRetraction (E : DerivedCategory (ModuleCat.{u} R))
    (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    (DerivedTensor.Right.sourceFunctor E).obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj
          (CellReplacement.replacement A)) ⟶
      (rightFunctor R E).obj
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj A)) :=
  (rightSourceFactors R (DerivedCategory.Q.objPreimage E)).hom.app
      (CellReplacement.replacement A) ≫
    (Localization.isoOfHom DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
      (HomologicalComplex.tensorHom
        (CellReplacement.augmentation (CellReplacement.replacement A))
        (CellReplacement.augmentation (DerivedCategory.Q.objPreimage E)))
      (tensorAugmentation_quasiIso R A (DerivedCategory.Q.objPreimage E))).inv ≫
    (fac R).inv.app (CellReplacement.replacement A, DerivedCategory.Q.objPreimage E) ≫
    (derived R).map (Prod.mkHom
      ((inputAugmentationIso A).hom ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app A)
      (DerivedCategory.Q.objObjPreimageIso E).hom)

/-- Compare the canonical localization with the caller's original derived-category model. -/
def localizationComparison :
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Localization ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  (Localization.uniq (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ))).functor

/-- The comparison between the two original localization functors. -/
def localizationComparisonIso :
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q ⋙
        localizationComparison R ≅ DerivedCategory.Qh :=
  Localization.compUniqFunctor (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ))

/-- Transport the specified right counit to the canonical localization. -/
def rightLocalCounit (E : DerivedCategory (ModuleCat.{u} R)) :
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q ⋙
        (localizationComparison R ⋙ rightFunctor R E) ⟶
      DerivedTensor.Right.sourceFunctor E :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (localizationComparisonIso R).hom (rightFunctor R E) ≫
    rightCounit R E

/-- The localization-indexed cone has the native tensor as its actual vertex and the
augmentation counit as its legs. -/
def rightCone (E : DerivedCategory (ModuleCat.{u} R))
    (X : HomotopyCategory (ModuleCat.{u} R) (up ℤ)) :
    Cone (StructuredArrow.proj
      ((HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q.obj X)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q ⋙
        DerivedTensor.Right.sourceFunctor E) :=
  (Functor.RightExtension.mk (localizationComparison R ⋙ rightFunctor R E)
    (rightLocalCounit R E)).coneAt
      ((HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q.obj X)

/-- The distinguished stage is the displayed cell replacement of the input, with its
specified augmentation formally inverted in the localization. -/
def rightStage (X : HomotopyCategory (ModuleCat.{u} R) (up ℤ)) :
    StructuredArrow ((HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q.obj X)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q :=
  StructuredArrow.mk (Localization.isoOfHom
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ))
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).map
      (CellReplacement.augmentation X.as))
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
      (CellReplacement.augmentation_quasiIso X.as))).inv

/-- The splitting retains the explicit tensor-augmentation inverse, rather than selecting an
inverse from an unproved `IsIso` assertion. -/
def rightSplit (E : DerivedCategory (ModuleCat.{u} R))
    (X : HomotopyCategory (ModuleCat.{u} R) (up ℤ)) :
    SplitMono ((rightCone R E X).π.app (rightStage R X)) where
  retraction := rightRetraction R E X.as ≫
    (rightFunctor R E).map ((localizationComparisonIso R).inv.app X)
  id := sorry

/-- Fixed-right source-definedness stores the actual cone, cell stage and splitting.
Only the eventual-factorization law is deferred. -/
theorem rightDefinedAt (E : DerivedCategory (ModuleCat.{u} R))
    (X : HomotopyCategory (ModuleCat.{u} R) (up ℤ)) :
    Functor.LeftDerived.DefinedAt (DerivedTensor.Right.sourceFunctor E)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)) X where
  isEssentiallyConstant := ⟨rightCone R E X, rightStage R X, rightSplit R E X, by
    intro j
    sorry⟩

/-- Koszul symmetry compares the two original fixed-factor source functors. -/
def sourceSymmetry (E : DerivedCategory (ModuleCat.{u} R)) :
    DerivedTensor.Right.sourceFunctor E ≅ DerivedTensor.Left.sourceFunctor E :=
  Functor.isoWhiskerRight
    (Functor.Homotopy.liftIso
      (Functor.Homotopy.BifunctorTotal.rightPreservesHomotopy
        (curriedTensor (ModuleCat.{u} R)) (DerivedCategory.Q.objPreimage E))
      (Functor.Homotopy.BifunctorTotal.leftPreservesHomotopy
        (curriedTensor (ModuleCat.{u} R)) (DerivedCategory.Q.objPreimage E))
      (BraidedCategory.tensorLeftIsoTensorRight (DerivedCategory.Q.objPreimage E)).symm)
    DerivedCategory.Qh

/-- Fixed-left source-definedness transports the actual right presentation through Koszul
symmetry, including its specified retraction. -/
theorem leftDefinedAt (E : DerivedCategory (ModuleCat.{u} R))
    (X : HomotopyCategory (ModuleCat.{u} R) (up ℤ)) :
    Functor.LeftDerived.DefinedAt (DerivedTensor.Left.sourceFunctor E)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)) X := by
  let e := Functor.isoWhiskerLeft
    (StructuredArrow.proj
      ((HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q.obj X)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)).Q) (sourceSymmetry R E)
  refine ⟨⟨(Cone.postcompose e.hom).obj (rightCone R E X), rightStage R X,
    { retraction := e.inv.app (rightStage R X) ≫ (rightSplit R E X).retraction
      id := by sorry }, ?_⟩⟩
  intro j
  sorry

/-- Evaluate a competing extension on the displayed cell replacement, then use the specified
stage retraction. This is the actual universal lift for the native fixed-right functor. -/
def rightExtensionLiftOnInput (E : DerivedCategory (ModuleCat.{u} R))
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (β : DerivedCategory.Qh ⋙ G ⟶ DerivedTensor.Right.sourceFunctor E)
    (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    G.obj (DerivedCategory.Q.obj A) ⟶ (rightFunctor R E).obj (DerivedCategory.Q.obj A) :=
  G.map (inputAugmentationIso A).inv ≫
    G.map ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app
      (CellReplacement.replacement A)) ≫
    β.app ((HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj
      (CellReplacement.replacement A)) ≫
    rightRetraction R E A ≫
    (rightFunctor R E).map
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app A)

/-- Descend the displayed lift formula along the original cochain localization. -/
def rightExtensionLift (E : DerivedCategory (ModuleCat.{u} R))
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (β : DerivedCategory.Qh ⋙ G ⟶ DerivedTensor.Right.sourceFunctor E) :
    G ⟶ rightFunctor R E :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
    (DerivedCategory.Q ⋙ G) (DerivedCategory.Q ⋙ rightFunctor R E) G (rightFunctor R E)
    { app := rightExtensionLiftOnInput R E G β
      naturality := by intros; sorry }

/-- Factorization through the native fixed-right counit. -/
theorem rightExtensionLift_fac (E : DerivedCategory (ModuleCat.{u} R))
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (β : DerivedCategory.Qh ⋙ G ⟶ DerivedTensor.Right.sourceFunctor E) :
    Functor.whiskerLeft DerivedCategory.Qh (rightExtensionLift R E G β) ≫
      rightCounit R E = β := sorry

/-- Uniqueness of the displayed fixed-right extension lift. -/
theorem rightExtensionLift_unique (E : DerivedCategory (ModuleCat.{u} R))
    (G : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (β : DerivedCategory.Qh ⋙ G ⟶ DerivedTensor.Right.sourceFunctor E)
    (γ : G ⟶ rightFunctor R E)
    (hγ : Functor.whiskerLeft DerivedCategory.Qh γ ≫ rightCounit R E = β) :
    γ = rightExtensionLift R E G β := sorry

/-- The native fixed-right extension is terminal with the displayed lifts. -/
def rightTerminalWitness (E : DerivedCategory (ModuleCat.{u} R)) :
    IsTerminal (Functor.RightExtension.mk (rightFunctor R E) (rightCounit R E)) :=
  IsTerminal.ofUniqueHom
    (fun G ↦ CostructuredArrow.homMk
      (rightExtensionLift R E G.left G.hom) (rightExtensionLift_fac R E G.left G.hom))
    (by
      intro G m
      apply CostructuredArrow.hom_ext
      exact rightExtensionLift_unique R E G.left G.hom m.left (by
        have h := m.w
        change Functor.whiskerLeft _ m.left ≫ rightCounit R E = G.hom ≫ 𝟙 _ at h
        exact h.trans (Category.comp_id _)))

/-- Fixed-right compatibility retains the actual universal lift in its proof witness. -/
instance right_isLeftDerived (E : DerivedCategory (ModuleCat.{u} R)) :
    (rightFunctor R E).IsLeftDerivedFunctor (rightCounit R E)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ)) where
  isRightKanExtension := ⟨⟨rightTerminalWitness R E⟩⟩

/-- The native comparison with the canonical selected bifunctor. -/
def canonicalIso [DerivedTensor.Bifunctor.Has (C := ModuleCat.{u} R)] :
    DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} R) ≅ derived R :=
  DerivedTensor.Bifunctor.modelIso (derived R) (homotopyCounit R)

/-- Curry the two actual comparison transformations at the fixed right argument. -/
def rightCanonicalIso [DerivedTensor.Bifunctor.Has (C := ModuleCat.{u} R)]
    (E : DerivedCategory (ModuleCat.{u} R)) :
    DerivedTensor.Bifunctor.rightFunctor E ≅ rightFunctor R E :=
  ((flipFunctor _ _ _).mapIso (Functor.curry.mapIso (canonicalIso R))).app E

/-- The curried model comparison preserves the original fixed-right counit. -/
theorem rightCanonicalIso_counit [DerivedTensor.Bifunctor.Has (C := ModuleCat.{u} R)]
    (E : DerivedCategory (ModuleCat.{u} R)) :
    Functor.whiskerLeft DerivedCategory.Qh (rightCanonicalIso R E).hom ≫ rightCounit R E =
      DerivedTensor.Bifunctor.Right.counitOf E := sorry

end DerivedTensorConstruction


/-- The ordinary tensor product of modules admits canonical unbounded fixed-factor derived tensor
functors. The stored presentations use the displayed semi-free cell replacements, augmentation
counits, and split stage legs in `DerivedTensorConstruction`. -/
@[stacks 064M "module category"]
instance hasDerivedTensor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedCategory.DerivedTensor.Has (C := ModuleCat.{u} R) where
  right := ⟨fun E ↦ ⟨DerivedTensorConstruction.rightDefinedAt R E⟩⟩
  left := ⟨fun E ↦ ⟨DerivedTensorConstruction.leftDefinedAt R E⟩⟩

/-- The tensor bifunctor on modules admits a canonical unbounded total left
derived bifunctor in both variables. -/
@[stacks 064M "module derived tensor bifunctor"]
instance hasDerivedTensorBifunctor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedCategory.DerivedTensor.Bifunctor.Has (C := ModuleCat.{u} R) :=
  Functor.HasLeftDerivedFunctor.mk'
    (LF := DerivedTensorConstruction.derived R)
    (α := DerivedTensorConstruction.homotopyCounit R)

/-- The canonical two-variable derived tensor on modules remains a left-derived model after
fixing its right argument.  This is the comparison gate between the bifunctor and fixed-right
owners; it does not assert that the ambient homotopy localization is strong monoidal. -/
@[stacks 064M "module fixed-right derived tensor compatibility"]
instance derivedTensorBifunctorRightCompatible (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (E : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory.DerivedTensor.Bifunctor.Right.Compatible E :=
  (Functor.isLeftDerivedFunctor_iff_of_iso
    (LF := DerivedCategory.DerivedTensor.Bifunctor.rightFunctor E)
    (LF' := DerivedTensorConstruction.rightFunctor R E)
    (α := DerivedCategory.DerivedTensor.Bifunctor.Right.counitOf E)
    (DerivedTensorConstruction.rightCounit R E)
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (up ℤ))
    (DerivedTensorConstruction.rightCanonicalIso R E)
    (DerivedTensorConstruction.rightCanonicalIso_counit R E)).mpr inferInstance

end ModuleCat

/- The ring-indexed notation is owned at the module instance boundary so downstream files that
  only need module-derived tensoring do not depend on the historical aggregation file.  Its body
  is the generic fixed-right object owner; `TensorProduct.lean` supplies the historical abbrev and
  bridge theorems separately. -/
namespace DerivedTensorProduct

set_option quotPrecheck false in
scoped notation:70 K:70 " ⊗[" R:70 "]^L " L:71 =>
  DerivedCategory.DerivedTensor.Right.obj (C := ModuleCat R) K L

end DerivedTensorProduct
