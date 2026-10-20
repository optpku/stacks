/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Unbounded derived adjunctions with an exact left adjoint

An exact left adjoint acts directly on unbounded derived categories.  For a Grothendieck-abelian
source of the right adjoint, the K-injective total right-derived owner supplies the right-hand
functor and its unit.  The only nonformal input is the absolute-derived pair condition required by
the general derived-adjunction theorem; the K-injective specialization installs that condition as
a named instance so callers do not rebuild proof-local `let` declarations.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe uC uD vC vD wC wD

namespace CategoryTheory.Adjunction.Derived.KInjective

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Abelian C] [Abelian D]
variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- The exact left action on an unbounded derived category. -/
@[stacks 015F "exact left action on unbounded derived categories"]
noncomputable abbrev left (L : C ⥤ₑ D) :
    DerivedCategory C ⥤ DerivedCategory D :=
  L.obj.mapDerivedCategory

/-- The K-injective total right-derived action of an additive functor. -/
@[stacks 05TH "K-injective unbounded right-derived action"]
noncomputable abbrev right (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] :
    DerivedCategory D ⥤ DerivedCategory C :=
  Functor.RightDerived.KInjective.functor R

/-- The localization factor of the exact left action. -/
@[stacks 015F "exact left derived factor"]
noncomputable abbrev leftFactor (L : C ⥤ₑ D) :
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⋙ left L ⟶
      L.obj.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D) :=
  L.obj.mapDerivedCategoryFactors.hom

/-- The cochain-level unit of the K-injective total right-derived action. -/
@[stacks 05TH "K-injective right-derived unit"]
noncomputable abbrev rightUnit (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] :
    R.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⟶
      (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D) ⋙ right R :=
  Functor.RightDerived.KInjective.unit R

/-- The exact left action is a left-derived functor of its homotopy action. -/
@[stacks 015F "exact action is left derived", instance]
noncomputable instance left_isLeftDerived (L : C ⥤ₑ D) :
    (left L).IsLeftDerivedFunctor (leftFactor L)
      (HomologicalComplex.quasiIso C (up ℤ)) := sorry

/-- The K-injective action is a right-derived functor of the homotopy action. -/
@[stacks 05TH "K-injective action is right derived", instance]
noncomputable instance right_isRightDerived (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] :
    (right R).IsRightDerivedFunctor (rightUnit R)
      (HomologicalComplex.quasiIso D (up ℤ)) := sorry

/-- The structure map for deriving the composite of the exact left action and the right action. -/
@[stacks 015F "exact-left/right-derived composite factor"]
noncomputable abbrev leftRightFactor (L : C ⥤ₑ D) (R : D ⥤ C)
    [R.Additive] [IsGrothendieckAbelian D] :
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C) ⋙
        (left L ⋙ right R) ⟶
      (L.obj.mapHomologicalComplex (up ℤ) ⋙
          (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)) ⋙ right R :=
  (Functor.associator (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
      (left L) (right R)).inv ≫
    Functor.whiskerRight (leftFactor L) (right R)

/-- The structure map for deriving the composite of the right action and the exact left action. -/
@[stacks 05TH "right-derived/exact-left composite unit"]
noncomputable abbrev rightLeftUnit (L : C ⥤ₑ D) (R : D ⥤ C)
    [R.Additive] [IsGrothendieckAbelian D] :
    (R.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)) ⋙ left L ⟶
      (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D) ⋙
        (right R ⋙ left L) :=
  Functor.whiskerRight (rightUnit R) (left L) ≫
    (Functor.associator (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)
      (right R) (left L)).hom

/-- The absolute-derived pair needed by the unbounded derived-adjunction construction. -/
@[stacks 015F "absolute unbounded derived pair"]
class HasPair (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] : Prop where
  /-- The exact-left/right-derived composite remains left derived. -/
  leftRight :
    (left L ⋙ right R).IsLeftDerivedFunctor (leftRightFactor L R)
      (HomologicalComplex.quasiIso C (up ℤ))
  /-- The right-derived/exact-left composite remains right derived. -/
  rightLeft :
    (right R ⋙ left L).IsRightDerivedFunctor (rightLeftUnit L R)
      (HomologicalComplex.quasiIso D (up ℤ))

attribute [instance] HasPair.leftRight HasPair.rightLeft

/-- The specified K-injective model is canonically isomorphic to the homotopy-defined total right-
derived functor. -/
private def rightModelIso (R : D ⥤ C) [R.Additive] [IsGrothendieckAbelian D] :
    Functor.KInjectiveModel.derived R ≅ right R :=
  @Functor.rightDerivedUnique _ _ _ _ _ _
    (Functor.KInjectiveModel.derived R) (right R) _ _
    (Functor.KInjectiveModel.Homotopy.unit R) (Functor.RightDerived.Homotopy.unit R)
    (HomotopyCategory.quasiIso D (up ℤ)) inferInstance
    (Functor.KInjectiveModel.Homotopy.isRightDerived R)
    (Functor.instIsRightDerivedFunctorTotalRightDerivedTotalRightDerivedUnit
      (Functor.Homotopy.toDerived R) DerivedCategory.Qh _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison of right-derived models carries the specified cochain unit to the total right-
derived unit. -/
private lemma rightModelIso_unit (R : D ⥤ C) [R.Additive] [IsGrothendieckAbelian D] :
    Functor.KInjectiveModel.unit R ≫
        Functor.whiskerLeft DerivedCategory.Q (rightModelIso R).hom = rightUnit R := by
  have h := Functor.rightDerivedNatTrans_fac
    (Functor.KInjectiveModel.derived R) (right R)
    (Functor.KInjectiveModel.Homotopy.unit R) (Functor.RightDerived.Homotopy.unit R)
    (HomotopyCategory.quasiIso D (up ℤ)) (𝟙 (Functor.Homotopy.toDerived R))
  have h0 : Functor.KInjectiveModel.Homotopy.unit R ≫
      Functor.whiskerLeft DerivedCategory.Qh (rightModelIso R).hom =
      Functor.RightDerived.Homotopy.unit R := by
    simpa only [rightModelIso, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Functor.rightDerivedNatTrans, Iso.refl_hom, Category.id_comp] using h
  ext A
  have hA := NatTrans.congr_app h0 ((HomotopyCategory.quotient D (up ℤ)).obj A)
  change (Functor.KInjectiveModel.Homotopy.unitOnCochains R).app A ≫
    (rightModelIso R).hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient D (up ℤ)).obj A)) = _ at hA
  dsimp only [Functor.KInjectiveModel.Homotopy.unitOnCochains,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_inv,
    Functor.associator_hom_app] at hA
  dsimp only [rightUnit, Functor.RightDerived.KInjective.unit,
    Functor.RightDerived.Homotopy.cochainUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rw [← hA]
  simp [Category.assoc, ← NatTrans.naturality]

/-- The localization factorization of an exact functor remains invertible after postcomposition. -/
private def leftRightIso (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive] [IsGrothendieckAbelian D] :
    DerivedCategory.Q ⋙ (left L ⋙ right R) ≅
      (L.obj.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q) ⋙ right R :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight L.obj.mapDerivedCategoryFactors (right R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Fully faithful localization supplies terminal right-extension data for the exact-left
composite. -/
private def leftRightWitness (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive] [IsGrothendieckAbelian D] :
    (Functor.RightExtension.mk (left L ⋙ right R) (leftRightFactor L R)).IsUniversal :=
  IsTerminal.ofUniqueHom
    (fun E ↦ CostructuredArrow.homMk
      ((Localization.fullyFaithfulWhiskeringLeft
        (DerivedCategory.Q (C := C)) (HomologicalComplex.quasiIso C (up ℤ))
        (DerivedCategory C)).preimage (E.hom ≫ (leftRightIso L R).inv)) (by
          change ((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q).map _ ≫
            (leftRightIso L R).hom = E.hom
          rw [(Localization.fullyFaithfulWhiskeringLeft
            (DerivedCategory.Q (C := C)) (HomologicalComplex.quasiIso C (up ℤ))
            (DerivedCategory C)).map_preimage]
          simp))
    (fun E m ↦ by
      apply CostructuredArrow.hom_ext
      apply (Localization.fullyFaithfulWhiskeringLeft
        (DerivedCategory.Q (C := C)) (HomologicalComplex.quasiIso C (up ℤ))
        (DerivedCategory C)).map_injective
      change ((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q).map m.left =
        ((Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q).map
          ((Localization.fullyFaithfulWhiskeringLeft
            (DerivedCategory.Q (C := C)) (HomologicalComplex.quasiIso C (up ℤ))
            (DerivedCategory C)).preimage (E.hom ≫ (leftRightIso L R).inv))
      rw [(Localization.fullyFaithfulWhiskeringLeft
        (DerivedCategory.Q (C := C)) (HomologicalComplex.quasiIso C (up ℤ))
        (DerivedCategory C)).map_preimage]
      have h := CostructuredArrow.w m
      change Functor.whiskerLeft _ m.left ≫ (leftRightIso L R).hom = E.hom at h
      rw [← h]
      simp)

/-- Exact application to the cochain-level image agrees with termwise application of the
composite. -/
private def compositeCochainIso (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive] :
    (R.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q) ⋙ left L ≅
      Functor.KInjectiveModel.ordinaryCochain (R ⋙ L.obj) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (R.mapHomologicalComplex (up ℤ))
      L.obj.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ L.obj)) (up ℤ))
      DerivedCategory.Q

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The K-injective exact-postcomposition isomorphism respects the specified augmentation units. -/
private lemma postcomposeIso_unit (L : C ⥤ₑ D) (R : D ⥤ C)
    [R.Additive] [IsGrothendieckAbelian D] :
    Functor.whiskerRight (Functor.KInjectiveModel.unit R) (left L) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft DerivedCategory.Q
          (Functor.KInjectiveModel.postcomposeIso R L.obj).hom =
      (compositeCochainIso L R).hom ≫ Functor.KInjectiveModel.unit (R ⋙ L.obj) := by
  ext A
  have h := (compositeCochainIso L R).hom.naturality
    ((CochainComplex.KInjectiveResolution.Construction.augmentation D).app A)
  simpa [Functor.KInjectiveModel.postcomposeIso,
    Functor.KInjectiveModel.postcomposeOnCochains,
    Functor.KInjectiveModel.postcomposeOnInput, Functor.KInjectiveModel.unit,
    compositeCochainIso, Localization.liftNatIso, Localization.liftNatTrans_app,
    Localization.Lifting.iso, left, Functor.comp_obj, Functor.comp_map,
    Functor.KInjectiveModel.ordinaryCochain, Category.assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp] using
    congrArg (fun f ↦ f ≫ (Functor.KInjectiveModel.fac (R ⋙ L.obj)).inv.app A) h

/-- The specified K-injective model of the composite agrees with exact postcomposition of the
total right-derived functor. -/
private def rightLeftModelIso (L : C ⥤ₑ D) (R : D ⥤ C)
    [R.Additive] [IsGrothendieckAbelian D] :
    Functor.KInjectiveModel.derived (R ⋙ L.obj) ≅ right R ⋙ left L :=
  (Functor.KInjectiveModel.postcomposeIso R L.obj).symm ≪≫
    Functor.isoWhiskerRight (rightModelIso R) (left L)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The composite-model isomorphism identifies its specified unit with the postcomposed right-
derived unit. -/
private lemma rightLeftModelIso_unit (L : C ⥤ₑ D) (R : D ⥤ C)
    [R.Additive] [IsGrothendieckAbelian D] :
    Functor.KInjectiveModel.unit (R ⋙ L.obj) ≫
        Functor.whiskerLeft DerivedCategory.Q (rightLeftModelIso L R).hom =
      (compositeCochainIso L R).inv ≫ rightLeftUnit L R := by
  ext A
  have hPost := NatTrans.congr_app (postcomposeIso_unit L R) A
  have hUnit := NatTrans.congr_app (rightModelIso_unit R) A
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app] at hPost hUnit
  dsimp only [rightLeftModelIso, rightLeftUnit, NatTrans.comp_app,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app]
  rw [← cancel_epi ((compositeCochainIso L R).hom.app A)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc ((compositeCochainIso L R).hom.app A), ← hPost]
  simp [Category.assoc, ← Functor.map_comp, hUnit]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Transport of the specified K-injective initial witness supplies universal extension maps for
exact postcomposition. -/
private def rightLeftWitness (L : C ⥤ₑ D) (R : D ⥤ C)
    [R.Additive] [IsGrothendieckAbelian D] :
    (Functor.LeftExtension.mk (right R ⋙ left L) (rightLeftUnit L R)).IsUniversal :=
  (Functor.LeftExtension.isUniversalEquivOfIso₂
    (Functor.LeftExtension.mk (Functor.KInjectiveModel.derived (R ⋙ L.obj))
      (Functor.KInjectiveModel.unit (R ⋙ L.obj)))
    (Functor.LeftExtension.mk (right R ⋙ left L) (rightLeftUnit L R))
    (compositeCochainIso L R).symm (rightLeftModelIso L R)
    (rightLeftModelIso_unit L R)) (Functor.KInjectiveModel.initialWitness (R ⋙ L.obj))

/-- K-injective resolutions provide the absolute-derived pair for an exact adjoint. -/
@[stacks 05TH "canonical K-injective absolute-derived pair", instance]
noncomputable instance hasPair (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] : HasPair L R where
  leftRight := { isRightKanExtension := ⟨⟨leftRightWitness L R⟩⟩ }
  rightLeft := { isLeftKanExtension := ⟨⟨rightLeftWitness L R⟩⟩ }

/-- The unbounded derived adjunction associated to an exact/K-injective adjoint pair. -/
@[stacks 05TH "unbounded derived adjunction for an exact left adjoint"]
noncomputable def adjunction (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [IsGrothendieckAbelian D] (adj : L.obj ⊣ R) :
    left L ⊣ right R :=
  @CategoryTheory.Adjunction.derived
    _ _ _ _ _ _ _ _ _ _
    (CategoryTheory.Adjunction.mapHomologicalComplexAdjunction adj (up ℤ))
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (DerivedCategory.Q : CochainComplex D ℤ ⥤ DerivedCategory D)
    (HomologicalComplex.quasiIso C (up ℤ))
    (HomologicalComplex.quasiIso D (up ℤ))
    inferInstance inferInstance
    (left L) (right R) (leftFactor L) (rightUnit R)
    (left_isLeftDerived L) (right_isRightDerived R)
    (HasPair.leftRight (L := L) (R := R))
    (HasPair.rightLeft (L := L) (R := R))

end CategoryTheory.Adjunction.Derived.KInjective

end
