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
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
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
      (CellReplacement.replacementMap a) (CellReplacement.replacementMap b)) := by
  have replacementMap_quasiIso {K L : CochainComplex (ModuleCat.{u} R) ℤ}
      (f : K ⟶ L) (hf : QuasiIso f) : QuasiIso (CellReplacement.replacementMap f) := by
    haveI := hf
    haveI := CellReplacement.augmentation_quasiIso K
    haveI := CellReplacement.augmentation_quasiIso L
    haveI : QuasiIso (CellReplacement.replacementMap f ≫ CellReplacement.augmentation L) := by
      rw [CellReplacement.replacementMap_augmentation]
      infer_instance
    exact quasiIso_of_comp_right _ (CellReplacement.augmentation L)
  haveI := CellReplacement.replacement_isKProjective A
  haveI := CellReplacement.replacement_isKProjective A'
  haveI := CellReplacement.replacement_isKProjective B
  haveI := CellReplacement.replacement_isKProjective B'
  exact homotopyEquivalences_le_quasiIso (ModuleCat.{u} R) (up ℤ) _
    ((homotopyEquivalences (ModuleCat.{u} R) (up ℤ)).tensorHom_mem _ _
      ((CochainComplex.IsKProjective.quasiIso_iff _).1 (replacementMap_quasiIso a ha))
      ((CochainComplex.IsKProjective.quasiIso_iff _).1 (replacementMap_quasiIso b hb)))

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

private theorem sourceFunctorObjIso_naturality
    {A A' B B' : CochainComplex (ModuleCat.{u} R) ℤ}
    (a : A ⟶ A') (b : B ⟶ B') :
    (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)).map
        (Prod.mkHom ((HomotopyCategory.quotient _ _).map a)
          ((HomotopyCategory.quotient _ _).map b)) ≫
        (DerivedTensor.Bifunctor.sourceFunctorObjIso A' B').hom =
      (DerivedTensor.Bifunctor.sourceFunctorObjIso A B).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom a b) := by
  have hmap :
      (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)).map
          (Prod.mkHom ((HomotopyCategory.quotient _ _).map a)
            ((HomotopyCategory.quotient _ _).map b)) =
        DerivedCategory.Qh.map
          (((HomotopyCategory.quotient _ _).map a) ⊗ₘ
            ((HomotopyCategory.quotient _ _).map b)) := by
    simp only [tensorHom_def, Functor.map_comp]
    rfl
  rw [hmap]
  change DerivedCategory.Qh.map
      (((HomotopyCategory.quotient _ _).map a) ⊗ₘ
        ((HomotopyCategory.quotient _ _).map b)) ≫
      (DerivedCategory.Qh.map (Functor.LaxMonoidal.μ
        (HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)) A' B') ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app (A' ⊗ B')) =
    (DerivedCategory.Qh.map (Functor.LaxMonoidal.μ
        (HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)) A B) ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app (A ⊗ B)) ≫
      DerivedCategory.Q.map (HomologicalComplex.tensorHom a b)
  rw [← Category.assoc, ← Functor.map_comp,
    Functor.LaxMonoidal.μ_natural, Functor.map_comp, Category.assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality]
  simp only [Category.assoc]
  rfl

/-- The transported augmentation components respect homotopy morphisms in both variables. -/
theorem homotopyCounitComponent_naturality
    {X Y : HomotopyCategory (ModuleCat.{u} R) (up ℤ) ×
      HomotopyCategory (ModuleCat.{u} R) (up ℤ)} (a : X ⟶ Y) :
    ((DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ derived R).map a ≫
        homotopyCounitComponent R Y =
      homotopyCounitComponent R X ≫ ((DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R))).map a := by
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)
  let e : (q.prod q) ⋙ DerivedTensor.Bifunctor.localization ≅
      (DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    NatIso.prod (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
  let s : (q.prod q) ⋙ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)) ≅
      MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun Z ↦ DerivedTensor.Bifunctor.sourceFunctorObjIso Z.1 Z.2)
      (fun f ↦ sourceFunctorObjIso_naturality R f.1 f.2)
  let τ : (q.prod q) ⋙ (DerivedTensor.Bifunctor.localization ⋙ derived R) ⟶
      (q.prod q) ⋙ DerivedTensor.Bifunctor.sourceFunctor :=
    Functor.whiskerRight e.hom (derived R) ≫ cochainCounit R ≫ s.inv
  rcases X with ⟨⟨A⟩, ⟨B⟩⟩
  rcases Y with ⟨⟨A'⟩, ⟨B'⟩⟩
  obtain ⟨f₁, hf₁⟩ := q.map_surjective a.1
  obtain ⟨f₂, hf₂⟩ := q.map_surjective a.2
  have ha : a = (q.prod q).map (Prod.mkHom f₁ f₂) := Prod.ext hf₁.symm hf₂.symm
  subst a
  exact τ.naturality (Prod.mkHom f₁ f₂)

/-- The natural augmentation from the localized cell model to the homotopy tensor source. -/
def homotopyCounit : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ derived R ⟶
    (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)) where
  app := homotopyCounitComponent R
  naturality := fun _ _ a ↦ homotopyCounitComponent_naturality R a

private theorem homotopyCounit_app (A B : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derived R).map (Prod.mkHom
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app A)
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app B)) ≫
      (homotopyCounit R).app
        ((HomotopyCategory.quotient _ _).obj A, (HomotopyCategory.quotient _ _).obj B) ≫
      (DerivedTensor.Bifunctor.sourceFunctorObjIso A B).hom =
    (cochainCounit R).app (A, B) := by
  let i := ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app A).prod
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app B)
  let c : (derived R).obj (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj (A ⊗ B) := (cochainCounit R).app (A, B)
  change (derived R).map i.inv ≫
    ((derived R).map i.hom ≫ c ≫ (DerivedTensor.Bifunctor.sourceFunctorObjIso A B).inv) ≫
      (DerivedTensor.Bifunctor.sourceFunctorObjIso A B).hom = c
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Functor.mapIso_hom, Functor.mapIso_inv] using
    ((derived R).mapIso i).inv_hom_id_assoc c

variable {R}

/-- Formally invert the specified cell augmentation of a cochain complex. -/
def inputAugmentationIso (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    (DerivedCategory.Q (C := ModuleCat.{u} R)).obj (CellReplacement.replacement A) ≅ (DerivedCategory.Q (C := ModuleCat.{u} R)).obj A :=
  Localization.isoOfHom (DerivedCategory.Q (C := ModuleCat.{u} R))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
    (CellReplacement.augmentation A) (CellReplacement.augmentation_quasiIso A)

private theorem replacementFunctor_obj (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CellReplacement.functor R).obj A = CellReplacement.replacement A := rfl

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
        (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ derived R).map a := by
  let F : CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
    CellReplacement.functor R
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)
  let e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q :=
    NatIso.ofComponents inputAugmentationIso (fun f ↦ by
      change DerivedCategory.Q.map (CellReplacement.replacementMap f) ≫
          DerivedCategory.Q.map (CellReplacement.augmentation _) =
        DerivedCategory.Q.map (CellReplacement.augmentation _) ≫ DerivedCategory.Q.map f
      simp only [← Functor.map_comp, CellReplacement.replacementMap_augmentation])
  let t : (q.prod q) ⋙ DerivedTensor.Bifunctor.localization ≅
      (DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    NatIso.prod (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
  let s : (q.prod q) ⋙ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)) ≅
      MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun Z ↦ DerivedTensor.Bifunctor.sourceFunctorObjIso Z.1 Z.2)
      (fun f ↦ sourceFunctorObjIso_naturality R f.1 f.2)
  let τ : (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ G) ⟶
      (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ derived R) :=
    Functor.whiskerRight (NatIso.prod e e).inv G ≫
      Functor.whiskerRight (Functor.whiskerLeft (F.prod F) t.inv) G ≫
      Functor.whiskerLeft ((F.prod F) ⋙ (q.prod q)) β ≫
      Functor.whiskerLeft (F.prod F) s.hom ≫ (fac R).inv
  exact τ.naturality a

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

private theorem extensionLift_app
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ G ⟶
      (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)))
    (Z : CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ) :
    (extensionLift G β).app (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod
      (DerivedCategory.Q (C := ModuleCat.{u} R))).obj Z) = extensionLiftOnInput G β Z := by
  exact (Localization.liftNatTrans_app
    ((DerivedCategory.Q (C := ModuleCat.{u} R)).prod DerivedCategory.Q)
    ((quasiIso (ModuleCat.{u} R) (up ℤ)).prod (quasiIso (ModuleCat.{u} R) (up ℤ)))
    (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod DerivedCategory.Q) ⋙ G)
    (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod DerivedCategory.Q) ⋙ derived R)
    G (derived R)
    { app := extensionLiftOnInput G β
      naturality := fun _ _ a ↦ extensionLiftOnInput_naturality G β a } Z).trans
    ((Category.id_comp _).trans (Category.comp_id _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The descended lift factors the given homotopy comparison through the augmentation counit. -/
theorem extensionLift_fac
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ G ⟶ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R))) :
    Functor.whiskerLeft (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) (extensionLift G β) ≫
      homotopyCounit R = β := by
  let F : CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
    CellReplacement.functor R
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)
  let t : (q.prod q) ⋙ DerivedTensor.Bifunctor.localization ≅
      (DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    NatIso.prod (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
  let s : (q.prod q) ⋙ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)) ≅
      MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun Z ↦ DerivedTensor.Bifunctor.sourceFunctorObjIso Z.1 Z.2)
      (fun f ↦ sourceFunctorObjIso_naturality R f.1 f.2)
  let η : ((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))) ⋙ G ⟶
      MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight t.inv G ≫ Functor.whiskerLeft (q.prod q) β ≫ s.hom
  have h (Z : CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ) :
      (extensionLift G β).app (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))).obj Z) ≫
        (cochainCounit R).app Z = η.app Z := by
    have happ : (extensionLift G β).app (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod (DerivedCategory.Q (C := ModuleCat.{u} R))).obj Z) =
        extensionLiftOnInput G β Z := by
      exact extensionLift_app G β Z
    rw [happ]
    let i := (inputAugmentationIso Z.1).prod (inputAugmentationIso Z.2)
    have hη := η.naturality
      (Prod.mkHom (CellReplacement.augmentation Z.1) (CellReplacement.augmentation Z.2))
    change G.map i.hom ≫ η.app Z = η.app ((F.prod F).obj Z) ≫
      DerivedCategory.Q.map (HomologicalComplex.tensorHom
        (CellReplacement.augmentation Z.1) (CellReplacement.augmentation Z.2)) at hη
    have H : G.map i.inv ≫ η.app ((F.prod F).obj Z) ≫
        DerivedCategory.Q.map (HomologicalComplex.tensorHom
          (CellReplacement.augmentation Z.1) (CellReplacement.augmentation Z.2)) = η.app Z := by
      exact (congrArg (fun f ↦ G.map i.inv ≫ f) hη.symm).trans
        ((G.mapIso i).inv_hom_id_assoc (η.app Z))
    change G.map i.inv ≫ η.app ((F.prod F).obj Z) ≫
      DerivedCategory.Q.map (CellReplacement.augmentation Z.1 ⊗ₘ
        CellReplacement.augmentation Z.2) = η.app Z at H
    simpa only [extensionLiftOnInput, cochainCounit, η, i, t, s, F, q,
      Iso.prod, NatIso.prod, NatIso.ofComponents, replacementFunctor_obj,
      CellReplacement.augmentationNatTrans, MonoidalCategory.tensor, Functor.prod_obj,
      NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map, Functor.comp_obj,
      NatTrans.prod, Category.assoc, Iso.inv_hom_id_app_assoc] using H
  have hε (Z : CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ) :
      (derived R).map (t.inv.app Z) ≫ (homotopyCounit R).app ((q.prod q).obj Z) ≫
        s.hom.app Z = (cochainCounit R).app Z := by
    exact homotopyCounit_app R Z.1 Z.2
  ext X
  rcases X with ⟨⟨A⟩, ⟨B⟩⟩
  apply (cancel_epi (G.map (t.inv.app (A, B)))).1
  apply (cancel_mono (s.hom.app (A, B))).1
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  have hn := congrArg (fun f ↦ f ≫
      (homotopyCounit R).app ((q.prod q).obj (A, B)) ≫ s.hom.app (A, B))
    ((extensionLift G β).naturality (t.inv.app (A, B)))
  have hc := congrArg (fun f ↦
      (extensionLift G β).app (((DerivedCategory.Q (C := ModuleCat.{u} R)).prod
        (DerivedCategory.Q (C := ModuleCat.{u} R))).obj (A, B)) ≫ f) (hε (A, B))
  simp only [Category.assoc] at hn hc
  simpa only [η, q, HomotopyCategory.quotient, Quotient.functor,
    Functor.prod_obj, Functor.comp_obj, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using
    hn.trans (hc.trans (h (A, B)))

private theorem quotient_replacementMap_augmentation
    (A : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).map
        (CellReplacement.replacementMap (CellReplacement.augmentation A)) =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).map
        (CellReplacement.augmentation (CellReplacement.replacement A)) := by
  haveI := CellReplacement.replacement_isKProjective (CellReplacement.replacement A)
  haveI := CellReplacement.augmentation_quasiIso A
  have hQ : DerivedCategory.Q.map
      (CellReplacement.replacementMap (CellReplacement.augmentation A)) =
      DerivedCategory.Q.map (CellReplacement.augmentation (CellReplacement.replacement A)) := by
    apply (cancel_mono (DerivedCategory.Q.map (CellReplacement.augmentation A))).1
    simp only [← Functor.map_comp, CellReplacement.replacementMap_augmentation]
  apply (CochainComplex.IsKProjective.Qh_map_bijective _ _).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app
    (CellReplacement.replacement A))).1
  calc
    _ = (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app
        (CellReplacement.replacement (CellReplacement.replacement A)) ≫
        DerivedCategory.Q.map (CellReplacement.replacementMap (CellReplacement.augmentation A)) :=
      DerivedCategory.quotientCompQhIso_hom_naturality _
    _ = (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app
        (CellReplacement.replacement (CellReplacement.replacement A)) ≫
        DerivedCategory.Q.map (CellReplacement.augmentation (CellReplacement.replacement A)) :=
      congrArg (fun f ↦ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app
        (CellReplacement.replacement (CellReplacement.replacement A)) ≫ f) hQ
    _ = _ := (DerivedCategory.quotientCompQhIso_hom_naturality _).symm

private theorem cochainCounit_replacement (A B : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainCounit R).app (CellReplacement.replacement A, CellReplacement.replacement B) =
      (derived R).map (Prod.mkHom
        (DerivedCategory.Q.map (CellReplacement.augmentation A))
        (DerivedCategory.Q.map (CellReplacement.augmentation B))) ≫ (fac R).hom.app (A, B) := by
  have hT : DerivedCategory.Q.map (HomologicalComplex.tensorHom
      (CellReplacement.replacementMap (CellReplacement.augmentation A))
      (CellReplacement.replacementMap (CellReplacement.augmentation B))) =
      DerivedCategory.Q.map (HomologicalComplex.tensorHom
        (CellReplacement.augmentation (CellReplacement.replacement A))
        (CellReplacement.augmentation (CellReplacement.replacement B))) := by
    apply (cancel_epi (DerivedTensor.Bifunctor.sourceFunctorObjIso
      (CellReplacement.replacement (CellReplacement.replacement A))
      (CellReplacement.replacement (CellReplacement.replacement B))).hom).1
    rw [← sourceFunctorObjIso_naturality R, ← sourceFunctorObjIso_naturality R,
      quotient_replacementMap_augmentation A, quotient_replacementMap_augmentation B]
  have h := (fac R).hom.naturality
    (Prod.mkHom (CellReplacement.augmentation A) (CellReplacement.augmentation B))
  change (derived R).map (Prod.mkHom
      (DerivedCategory.Q.map (CellReplacement.augmentation A))
      (DerivedCategory.Q.map (CellReplacement.augmentation B))) ≫ (fac R).hom.app (A, B) =
    (fac R).hom.app (CellReplacement.replacement A, CellReplacement.replacement B) ≫
      DerivedCategory.Q.map (HomologicalComplex.tensorHom
        (CellReplacement.replacementMap (CellReplacement.augmentation A))
        (CellReplacement.replacementMap (CellReplacement.augmentation B))) at h
  exact (congrArg (fun f ↦ (fac R).hom.app
    (CellReplacement.replacement A, CellReplacement.replacement B) ≫ f) hT.symm).trans h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem cochainCounit_fac
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : DerivedTensor.Bifunctor.localization ⋙ G ⟶ DerivedTensor.Bifunctor.sourceFunctor)
    (γ : G ⟶ derived R)
    (hγ : Functor.whiskerLeft DerivedTensor.Bifunctor.localization γ ≫ homotopyCounit R = β)
    (A B : CochainComplex (ModuleCat.{u} R) ℤ) :
    γ.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫ (cochainCounit R).app (A, B) =
      G.map (Prod.mkHom
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app A)
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app B)) ≫
      β.app ((HomotopyCategory.quotient _ _).obj A, (HomotopyCategory.quotient _ _).obj B) ≫
      (DerivedTensor.Bifunctor.sourceFunctorObjIso A B).hom := by
  let i := ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app A).prod
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app B)
  let X := ((HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj A,
    (HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj B)
  let s := DerivedTensor.Bifunctor.sourceFunctorObjIso A B
  have hc := congrArg (fun f ↦ G.map i.inv ≫ f ≫ s.hom) (congr_app hγ X)
  have hn := congrArg (fun f ↦ f ≫ (homotopyCounit R).app X ≫ s.hom)
    (γ.naturality i.inv)
  have hε := congrArg (fun f ↦ γ.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫ f)
    (homotopyCounit_app R A B)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc] at hc hn hε
  exact hε.symm.trans (hn.symm.trans hc)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The specified lift is the unique factorization through the augmentation counit. -/
theorem extensionLift_unique
    (G : DerivedCategory (ModuleCat.{u} R) × DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (β : (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) ⋙ G ⟶ (DerivedTensor.Bifunctor.sourceFunctor (C := ModuleCat.{u} R)))
    (γ : G ⟶ derived R)
    (hγ : Functor.whiskerLeft (DerivedTensor.Bifunctor.localization (C := ModuleCat.{u} R)) γ ≫ homotopyCounit R = β) :
    γ = extensionLift G β := by
  let F : CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
    CellReplacement.functor R
  let q := HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)
  let Qp := (DerivedCategory.Q (C := ModuleCat.{u} R)).prod
    (DerivedCategory.Q (C := ModuleCat.{u} R))
  let t : (q.prod q) ⋙ DerivedTensor.Bifunctor.localization ≅ Qp :=
    NatIso.prod (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))
  let s : (q.prod q) ⋙ DerivedTensor.Bifunctor.sourceFunctor ≅
      MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun Z ↦ DerivedTensor.Bifunctor.sourceFunctorObjIso Z.1 Z.2)
      (fun f ↦ sourceFunctorObjIso_naturality R f.1 f.2)
  let η : Qp ⋙ G ⟶
      MonoidalCategory.tensor (CochainComplex (ModuleCat.{u} R) ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight t.inv G ≫ Functor.whiskerLeft (q.prod q) β ≫ s.hom
  have hγQ (Z : CochainComplex (ModuleCat.{u} R) ℤ × CochainComplex (ModuleCat.{u} R) ℤ) :
      γ.app (Qp.obj Z) ≫ (cochainCounit R).app Z = η.app Z := by
    exact cochainCounit_fac G β γ hγ Z.1 Z.2
  apply Localization.natTrans_ext Qp
    ((quasiIso (ModuleCat.{u} R) (up ℤ)).prod (quasiIso (ModuleCat.{u} R) (up ℤ)))
  intro Z
  have happ : (extensionLift G β).app (Qp.obj Z) = extensionLiftOnInput G β Z := by
    exact extensionLift_app G β Z
  rw [happ]
  let i := (inputAugmentationIso Z.1).prod (inputAugmentationIso Z.2)
  have H : γ.app (Qp.obj Z) =
      G.map i.inv ≫ η.app ((F.prod F).obj Z) ≫ (fac R).inv.app Z := by
    rw [← hγQ]
    have hC := congrArg (fun f ↦ G.map i.inv ≫
        (γ.app (Qp.obj ((F.prod F).obj Z)) ≫ f) ≫ (fac R).inv.app Z)
      (cochainCounit_replacement Z.1 Z.2)
    have hn := congrArg (fun f ↦ G.map i.inv ≫ f) (γ.naturality i.hom).symm
    have H' : G.map i.inv ≫ γ.app (Qp.obj ((F.prod F).obj Z)) ≫
        (derived R).map i.hom = γ.app (Qp.obj Z) :=
      hn.trans ((G.mapIso i).inv_hom_id_assoc (γ.app (Qp.obj Z)))
    refine Eq.trans ?_ hC.symm
    simpa only [i, Iso.prod, inputAugmentationIso, Localization.isoOfHom_hom,
      Qp, Functor.prod_obj, Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using H'.symm
  simpa only [extensionLiftOnInput, η, i, t, s, F, q, Qp, Iso.prod, NatIso.prod,
    NatIso.ofComponents, replacementFunctor_obj, Functor.prod_obj, Functor.comp_obj,
    NatTrans.comp_app, NatTrans.prod, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] using H

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
      fromCellModel R ≫ toCellModel R = 𝟙 _ := by
  constructor
  · apply (DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} R)).leftDerived_ext
      (DerivedTensor.Bifunctor.counit (C := ModuleCat.{u} R))
      (DerivedTensor.Bifunctor.qis (C := ModuleCat.{u} R)) _ _ _
    simp only [Functor.whiskerLeft_comp, Category.assoc, fromCellModel,
      Functor.leftDerived_fac, toCellModel, extensionLift_fac,
      Functor.whiskerLeft_id', Category.id_comp]
  · apply (derived R).leftDerived_ext (homotopyCounit R)
      (DerivedTensor.Bifunctor.qis (C := ModuleCat.{u} R)) _ _ _
    simp only [Functor.whiskerLeft_comp, Category.assoc, toCellModel,
      extensionLift_fac, fromCellModel, Functor.leftDerived_fac,
      Functor.whiskerLeft_id', Category.id_comp]

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
      (CellReplacement.augmentation P) (CellReplacement.augmentation L)) := by
  haveI := CellReplacement.augmentation_quasiIso P
  haveI := CellReplacement.augmentation_quasiIso L
  haveI := CochainComplex.IsKFlat.quasiIso_tensorHom_left
    (replacement_isKFlat L)
    (CellReplacement.augmentation P)
  haveI := CochainComplex.IsKFlat.quasiIso_tensorHom_left hP (CellReplacement.augmentation L)
  let e : Arrow.mk (HomologicalComplex.tensorHom (𝟙 P)
      (CellReplacement.augmentation L)) ≅
      Arrow.mk (HomologicalComplex.tensorHom (CellReplacement.augmentation L) (𝟙 P)) :=
    Arrow.isoMk (β_ P (CellReplacement.replacement L)) (β_ P L) (by
      change (β_ P (CellReplacement.replacement L)).hom ≫
          (CellReplacement.augmentation L ⊗ₘ 𝟙 P) =
        (𝟙 P ⊗ₘ CellReplacement.augmentation L) ≫ (β_ P L).hom
      exact (CategoryTheory.BraidedCategory.braiding_naturality
        (𝟙 P) (CellReplacement.augmentation L)).symm)
  haveI : QuasiIso (HomologicalComplex.tensorHom (𝟙 P)
      (CellReplacement.augmentation L)) :=
    ((HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ)).arrow_mk_iso_iff e).2
      (show QuasiIso (HomologicalComplex.tensorHom
        (CellReplacement.augmentation L) (𝟙 P)) from inferInstance)
  haveI := quasiIso_comp (HomologicalComplex.tensorHom
      (CellReplacement.augmentation P)
      (𝟙 (CellReplacement.replacement L)))
    (HomologicalComplex.tensorHom (𝟙 P) (CellReplacement.augmentation L))
  change QuasiIso ((CellReplacement.augmentation P ⊗ₘ
      𝟙 (CellReplacement.replacement L)) ≫
    (𝟙 P ⊗ₘ CellReplacement.augmentation L)) at this
  change QuasiIso (CellReplacement.augmentation P ⊗ₘ
    CellReplacement.augmentation L)
  simpa only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    using this

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical tensor counit and the displayed K-flat inverse are mutual inverses. -/
theorem counitIsoOfKFlatLeft_laws (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : P.IsKFlat) :
    DerivedTensor.Bifunctor.counitAppOfQ P L ≫ counitInvOfKFlatLeft P L hP = 𝟙 _ ∧
      counitInvOfKFlatLeft P L hP ≫ DerivedTensor.Bifunctor.counitAppOfQ P L = 𝟙 _ := by
  let e : DerivedTensor.Bifunctor.obj (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (P ⊗ L) :=
    (canonicalIso R).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L) ≪≫
    (fac R).app (P, L) ≪≫
      Localization.isoOfHom (DerivedCategory.Q (C := ModuleCat.{u} R))
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (up ℤ))
        (HomologicalComplex.tensorHom (CellReplacement.augmentation P) (CellReplacement.augmentation L))
        (tensorAugmentation_quasiIso P L hP)
  have h := cochainCounit_fac
    (DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} R))
    (DerivedTensor.Bifunctor.counit (C := ModuleCat.{u} R)) (toCellModel R)
    (extensionLift_fac _ _) P L
  have hh : (toCellModel R).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L) ≫
      (cochainCounit R).app (P, L) = DerivedTensor.Bifunctor.counitAppOfQ P L := by
    simpa only [DerivedTensor.Bifunctor.counitAppOfQ, DerivedTensor.Bifunctor.counitAppOfComplex,
      DerivedTensor.Bifunctor.counitApp, Category.assoc] using h
  have he : e.hom = DerivedTensor.Bifunctor.counitAppOfQ P L := by
    have hformula : e.hom = (toCellModel R).app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L) ≫ (cochainCounit R).app (P, L) := by
      simp only [e, Iso.trans_hom, Iso.app_hom, canonicalIso, cochainCounit,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map,
        Localization.isoOfHom_hom]
      rfl
    exact hformula.trans hh
  have hi : e.inv = counitInvOfKFlatLeft P L hP := by
    simp only [e, Iso.trans_inv, Iso.app_inv, canonicalIso, counitInvOfKFlatLeft, Category.assoc]
  constructor
  · simpa only [he, hi] using e.hom_inv_id
  · simpa only [he, hi] using e.inv_hom_id

/-- Ordinary tensor with a K-flat left factor computes derived tensor, with its canonical counit. -/
def counitIsoOfKFlatLeft (P L : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.IsKFlat) :
    DerivedTensor.Bifunctor.obj ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj P) ((DerivedCategory.Q (C := ModuleCat.{u} R)).obj L) ≅
      (DerivedCategory.Q (C := ModuleCat.{u} R)).obj (P ⊗ L) where
  hom := DerivedTensor.Bifunctor.counitAppOfQ P L
  inv := counitInvOfKFlatLeft P L hP
  hom_inv_id := (counitIsoOfKFlatLeft_laws P L hP).1
  inv_hom_id := (counitIsoOfKFlatLeft_laws P L hP).2

end ModuleCat.DerivedTensorCellModel
