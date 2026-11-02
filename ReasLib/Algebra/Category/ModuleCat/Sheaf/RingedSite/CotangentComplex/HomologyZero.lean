/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Degree-zero homology of the sheaf cotangent complex

The cochain augmentation `L(φ) ⟶ Ω(φ)[0]` is the sheaf-level analogue of the ring-level
comparison: its degree-zero component is Kähler base change along the
standard-resolution augmentation, and the induced map on `H^0` identifies `L(φ).homology 0`
with `Ω(φ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open AlgebraicTopology
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.CotangentComplex
open scoped Simplicial RelativeDerivation

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The standard-resolution augmentation `P_n ⟶ B` is a morphism of objects of `Under A`. -/
theorem standardAugmentation_w (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    𝟙 A ≫ B.hom = (standardTerm A B n).hom ≫ standardAugmentation A B n :=
  ((standardResolution A B).hom.app n).w.symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The first degree-one face applies the comonad to the counit. -/
private theorem standardMap_face_zero (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    standardMap A B (SimplexCategory.δ (0 : Fin 2)).op =
      (freeForgetAdjunction A).toComonad.map ((freeForgetAdjunction A).counit.app B) := by
  change ((freeForgetAdjunction A).toComonad.simplicialResolution.δ (0 : Fin 2)).app B = _
  erw [Comonad.simplicialResolution.face]
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The second degree-one face is the counit at degree zero. -/
private theorem standardMap_face_one (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    standardMap A B (SimplexCategory.δ (1 : Fin 2)).op =
      (freeForgetAdjunction A).counit.app (standardTerm A B (op ⦋0⦌)) := by
  change ((freeForgetAdjunction A).toComonad.simplicialResolution.δ (1 : Fin 2)).app B = _
  erw [Comonad.simplicialResolution.face]
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The first face of a bracket is the bracket of its augmentation. -/
private theorem standardMap_face_zero_generator (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (X : Cᵒᵖ) (x : (standardTerm A B (op ⦋0⦌)).right.obj.obj X) :
    (standardMap A B (SimplexCategory.δ (0 : Fin 2)).op).right.hom.app X
      ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A
        (standardTerm A B (op ⦋0⦌))).hom.app X x) =
      (CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A B).hom.app X
        ((standardAugmentation A B (op ⦋0⦌)).hom.app X x) := by
  erw [standardMap_face_zero]
  let adj := freeForgetAdjunction A
  let V := Under.forget A ⋙ sheafCompose J (CategoryTheory.forget CommRingCat.{u})
  exact (congrArg (fun k => k.hom.app X x)
    (adj.unit.naturality (V.map (adj.counit.app B)))).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The second face evaluates a bracket to its label. -/
private theorem standardMap_face_one_generator (A : Sheaf J CommRingCat.{u}) (B : Under A)
    (X : Cᵒᵖ) (x : (standardTerm A B (op ⦋0⦌)).right.obj.obj X) :
    (standardMap A B (SimplexCategory.δ (1 : Fin 2)).op).right.hom.app X
      ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A
        (standardTerm A B (op ⦋0⦌))).hom.app X x) = x := by
  erw [standardMap_face_one]
  exact congrArg (fun k => k.hom.app X x)
    ((freeForgetAdjunction A).right_triangle_components (standardTerm A B (op ⦋0⦌)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The standard augmentation evaluates a canonical bracket to its label. -/
theorem standardAugmentation_generator {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (b : B.obj.obj X) :
    (standardAugmentation A (Under.mk φ) (op ⦋0⦌)).hom.app X
      ((eqToHom (standardResolution_obj_zero A (Under.mk φ)).symm).right.hom.app X
        ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A (Under.mk φ)).hom.app X b)) =
        b := by
  have hzero : (standardResolution A (Under.mk φ)).hom.app (op ⦋0⦌) =
      (freeForgetAdjunction A).counit.app (Under.mk φ) := by rfl
  change (standardAugmentation A (Under.mk φ) (op ⦋0⦌)).hom.app X
    ((CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A (Under.mk φ)).hom.app X b) = b
  change (((standardResolution A (Under.mk φ)).hom.app (op ⦋0⦌)).right).hom.app X _ = b
  rw [hzero]
  exact congrArg (fun k => k.hom.app X b)
    ((freeForgetAdjunction A).right_triangle_components (Under.mk φ))

/-- The Kähler base-change map `Ω_{P_0/A} ⊗_{P_0} B ⟶ Ω(φ)` along the standard-resolution
augmentation. -/
def standardToKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (simplicialModule A (Under.mk φ)).obj (op ⦋0⦌) ⟶ Ω(φ) :=
  ((ChangeOfRings.extendRestrictAdjunction
      (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).homEquiv _ _).symm
    (RelativeDifferentials.map
      ⟨standardAugmentation_w A (Under.mk φ) (op ⦋0⦌)⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension of the augmentation sends a universal differential to its image. -/
theorem standardToKaehler_unit_d {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (x : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X) :
    (standardToKaehler φ).val.app X
      (((ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).unit.app
          (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom)).val.app X
        ((relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).d x)) =
      (relativeDifferential φ).d
        ((standardAugmentation A (Under.mk φ) (op ⦋0⦌)).hom.app X x) := by
  let adj := ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))
  change ((adj.homEquiv _ _) (standardToKaehler φ)).val.app X
    ((relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).d x) = _
  rw [show (adj.homEquiv _ _) (standardToKaehler φ) =
      RelativeDifferentials.map ⟨standardAugmentation_w A (Under.mk φ) (op ⦋0⦌)⟩ from
    (adj.homEquiv _ _).apply_symm_apply _]
  exact RelativeDifferentials.map_d _ X x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A simplicial module map takes an extended universal differential to the differential of
its image under the corresponding algebra map. -/
theorem simplicialModuleMap_unit_d (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (X : Cᵒᵖ)
    (x : (standardTerm A B n).right.obj.obj X) :
    (simplicialModuleMap A B f).val.app X
      (((ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (standardAugmentation A B n))).unit.app
          (relativeDifferentials (standardTerm A B n).hom)).val.app X
        ((relativeDifferential (standardTerm A B n).hom).d x)) =
      ((ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (standardAugmentation A B m))).unit.app
          (relativeDifferentials (standardTerm A B m).hom)).val.app X
        ((relativeDifferential (standardTerm A B m).hom).d
          ((standardMap A B f).right.hom.app X x)) := by
  let adj := ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A B n))
  change ((adj.homEquiv _ _) (simplicialModuleMap A B f)).val.app X
    ((relativeDifferential (standardTerm A B n).hom).d x) = _
  rw [show (adj.homEquiv _ _) (simplicialModuleMap A B f) = _ from
    (adj.homEquiv _ _).apply_symm_apply _]
  change ((ChangeOfRings.extendRestrictAdjunction
      (ringSheafMap (standardAugmentation A B m))).unit.app
        (relativeDifferentials (standardTerm A B m).hom)).val.app X
      ((simplicialDifferentialsMap A B f).val.app X
        ((relativeDifferential (standardTerm A B n).hom).d x)) = _
  congr 1
  exact RelativeDifferentials.map_d _ X x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every simplicial map to degree zero is compatible with Kähler augmentation. -/
theorem simplicialModuleMap_comp_standardToKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    {n : SimplexCategoryᵒᵖ} (f : n ⟶ op ⦋0⦌) :
    simplicialModuleMap A (Under.mk φ) f ≫ standardToKaehler φ =
      ((ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (standardAugmentation A (Under.mk φ) n))).homEquiv _ _).symm
        (RelativeDifferentials.map ⟨standardAugmentation_w A (Under.mk φ) n⟩) := by
  let adj := ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) n))
  apply (adj.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply]
  apply relativeDifferential_postcomp_injective (standardTerm A (Under.mk φ) n).hom
  ext X x
  change (standardToKaehler φ).val.app X
      ((simplicialModuleMap A (Under.mk φ) f).val.app X
        ((adj.unit.app _).val.app X
          ((relativeDifferential (standardTerm A (Under.mk φ) n).hom).d x))) =
    (RelativeDifferentials.map ⟨standardAugmentation_w A (Under.mk φ) n⟩).val.app X
      ((relativeDifferential (standardTerm A (Under.mk φ) n).hom).d x)
  let sq : CommSq (𝟙 A) (standardTerm A (Under.mk φ) n).hom φ
      (standardAugmentation A (Under.mk φ) n) :=
    ⟨standardAugmentation_w A (Under.mk φ) n⟩
  have haug := congrArg
    (fun k : standardTerm A (Under.mk φ) n ⟶ Under.mk φ => k.right.hom.app X x)
    ((standardResolution A (Under.mk φ)).hom.naturality f)
  exact (congrArg ((standardToKaehler φ).val.app X)
    (simplicialModuleMap_unit_d A (Under.mk φ) f X x)).trans
      ((standardToKaehler_unit_d φ X ((standardMap A (Under.mk φ) f).right.hom.app X x)).trans
        ((congrArg (relativeDifferential φ).d haug).trans
          (RelativeDifferentials.map_d sq X x).symm))

/-- The degree-zero component of the canonical cochain comparison `L(φ) ⟶ Ω(φ)[0]`, obtained by
transporting Kähler base change of the standard-resolution augmentation along `objXIso`. -/
def toKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).X 0 ⟶ Ω(φ) :=
  (objXIso A (Under.mk φ) 0).hom ≫ standardToKaehler φ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The incoming differential in degree zero is the difference of the two simplicial faces. -/
theorem d_neg_one_zero {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) : L(φ).d (-1) 0 =
      (objXIso A (Under.mk φ) 1).hom ≫
        ((simplicialModule A (Under.mk φ)).δ (0 : Fin 2) -
          (simplicialModule A (Under.mk φ)).δ (1 : Fin 2)) ≫
        (objXIso A (Under.mk φ) 0).inv := by
  calc
    _ = (objXIso A (Under.mk φ) 1).hom ≫
        (AlternatingFaceMapComplex.obj (simplicialModule A (Under.mk φ))).d 1 0 ≫
          (objXIso A (Under.mk φ) 0).inv :=
      HomologicalComplex.extend_d_eq
        ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J B))).obj
          (simplicialModule A (Under.mk φ)))
        ComplexShape.embeddingDownNat (i := 1) (j := 0) rfl rfl
    _ = _ := by
      have hfaces : (AlternatingFaceMapComplex.obj (simplicialModule A (Under.mk φ))).d 1 0 =
          (simplicialModule A (Under.mk φ)).δ (0 : Fin 2) -
            (simplicialModule A (Under.mk φ)).δ (1 : Fin 2) := by
        have hsum : (AlternatingFaceMapComplex.obj (simplicialModule A (Under.mk φ))).d 1 0 =
            ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (simplicialModule A (Under.mk φ)).δ i :=
          AlternatingFaceMapComplex.obj_d_eq (simplicialModule A (Under.mk φ)) 0
        calc
          _ = _ := hsum
          _ = _ := by
            rw [Fin.sum_univ_two]
            simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
              one_zsmul, neg_one_zsmul, sub_eq_add_neg]
      exact congrArg (fun d => (objXIso A (Under.mk φ) 1).hom ≫ d ≫
        (objXIso A (Under.mk φ) 0).inv) hfaces

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The incoming differential of `L(φ)` into degree zero followed by `toKaehler` is zero. -/
theorem d_comp_toKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (i : ℤ) (h : (ComplexShape.up ℤ).Rel i 0) :
    L(φ).d i 0 ≫ toKaehler φ = 0 := by
  have hi : i = -1 := by
    change i + 1 = 0 at h
    omega
  subst i
  have hf : (simplicialModule A (Under.mk φ)).δ (0 : Fin 2) ≫ standardToKaehler φ =
      (simplicialModule A (Under.mk φ)).δ (1 : Fin 2) ≫ standardToKaehler φ :=
    (simplicialModuleMap_comp_standardToKaehler φ (SimplexCategory.δ (0 : Fin 2)).op).trans
      (simplicialModuleMap_comp_standardToKaehler φ (SimplexCategory.δ (1 : Fin 2)).op).symm
  have hd := d_neg_one_zero φ
  rw [hd]
  simp only [toKaehler, Category.assoc, Iso.inv_hom_id_assoc,
    Preadditive.sub_comp, hf, sub_self, comp_zero]

/-- The canonical cochain comparison `L(φ) ⟶ Ω(φ)[0]`. -/
def augmentation {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ) ⟶ (single (SheafOfModules (ringSheaf J B)) (ComplexShape.up ℤ) 0).obj Ω(φ) :=
  mkHomToSingle (toKaehler φ) (d_comp_toKaehler φ)

/-- The degree-zero component of `augmentation` is `toKaehler` followed by the inverse of
`singleObjXSelf`. -/
theorem augmentation_f_zero {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (augmentation φ).f 0 =
      toKaehler φ ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 (Ω(φ))).inv :=
  mkHomToSingle_f _ _

/-- The canonical map `H^0(L(φ)) ⟶ Ω(φ)` induced by `augmentation`. -/
def homologyZeroMap {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).homology 0 ⟶ Ω(φ) :=
  homologyMap (augmentation φ) 0 ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (Ω(φ))).hom

/-- Every degree-zero section determines a homology class, since the complex vanishes in
positive degrees. -/
def toHomologyZero {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).X 0 ⟶ L(φ).homology 0 :=
  L(φ).liftCycles (𝟙 _) 1 (by simp)
    (by
      apply (isZero_obj_X_of_pos A (Under.mk φ) (n := 1) (by decide)).eq_of_tgt) ≫
    L(φ).homologyπ 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Boundaries in degree zero have zero homology class. -/
theorem d_comp_toHomologyZero {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).d (-1) 0 ≫ toHomologyZero φ = 0 := by
  dsimp only [toHomologyZero]
  erw [← Category.assoc, comp_liftCycles]
  simpa only [Category.comp_id] using
    L(φ).liftCycles_homologyπ_eq_zero_of_boundary (L(φ).d (-1) 0) 1
      (by simp) (𝟙 _) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The two simplicial faces induce the same degree-zero homology class. -/
private theorem faces_comp_toHomologyZero {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (simplicialModule A (Under.mk φ)).δ (0 : Fin 2) ≫
        (objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ =
      (simplicialModule A (Under.mk φ)).δ (1 : Fin 2) ≫
        (objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ := by
  have h := d_comp_toHomologyZero φ
  erw [d_neg_one_zero] at h
  apply sub_eq_zero.mp
  rw [← Preadditive.sub_comp]
  apply (cancel_epi (objXIso A (Under.mk φ) 1).hom).mp
  simpa only [Category.assoc, comp_zero] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every degree-zero homology class is locally represented by a degree-zero section. -/
theorem toHomologyZero_epi {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    Epi (toHomologyZero φ) := by
  have hz : 𝟙 (L(φ).X 0) ≫ L(φ).d 0 1 = 0 :=
    (isZero_obj_X_of_pos A (Under.mk φ) (n := 1) (by decide)).eq_of_tgt _ _
  let p := L(φ).liftCycles (𝟙 _) 1 (by simp) hz
  have hp : L(φ).iCycles 0 ≫ p = 𝟙 _ := by
    apply (cancel_mono (L(φ).iCycles 0)).mp
    simp only [Category.assoc, liftCycles_i, Category.comp_id, Category.id_comp, p]
  letI : Epi p := epi_of_epi_fac hp
  change Epi (p ≫ L(φ).homologyπ 0)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation sends the class of a degree-zero section to its Kähler image. -/
@[reassoc (attr := simp)]
theorem toHomologyZero_comp_homologyZeroMap {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    toHomologyZero φ ≫ homologyZeroMap φ = toKaehler φ := by
  dsimp only [toHomologyZero, homologyZeroMap, Under.mk]
  erw [Category.assoc, homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom,
    cyclesMap_i_assoc, liftCycles_i_assoc, Category.id_comp,
    augmentation_f_zero, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The homology class of the differential of the canonical polynomial bracket of a section,
after extending scalars along the standard-resolution augmentation. -/
def homologyZeroGenerator {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (b : B.obj.obj X) : (L(φ).homology 0).val.obj X :=
  let bracket := (CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator
    A (Under.mk φ)).hom.app X b
  let x := (eqToHom (standardResolution_obj_zero A (Under.mk φ)).symm).right.hom.app
    X bracket
  let dx := (relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).d x
  let dxB := ((ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).unit.app
      (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom)).val.app X dx
  (toHomologyZero φ).val.app X ((objXIso A (Under.mk φ) 0).inv.val.app X dxB)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A polynomial differential and the bracket of its augmented section have the same homology class. -/
theorem polynomialDifferential_class {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (x : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X) :
    (toHomologyZero φ).val.app X ((objXIso A (Under.mk φ) 0).inv.val.app X
      (((ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).unit.app
          (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom)).val.app X
        ((relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).d x))) =
      homologyZeroGenerator φ X
        ((standardAugmentation A (Under.mk φ) (op ⦋0⦌)).hom.app X x) := by
  let bracket := (CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A
    (standardTerm A (Under.mk φ) (op ⦋0⦌))).hom.app X x
  let η := (ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋1⦌)))).unit.app
      (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋1⦌)).hom)
  let dx := (relativeDifferential (standardTerm A (Under.mk φ) (op ⦋1⦌)).hom).d bracket
  have hf := congrArg (fun k => k.val.app X (η.val.app X dx))
    (faces_comp_toHomologyZero φ)
  change ((objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ).val.app X
      ((simplicialModuleMap A (Under.mk φ) (SimplexCategory.δ (0 : Fin 2)).op).val.app X
        (η.val.app X dx)) =
    ((objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ).val.app X
      ((simplicialModuleMap A (Under.mk φ) (SimplexCategory.δ (1 : Fin 2)).op).val.app X
        (η.val.app X dx)) at hf
  have h0 := simplicialModuleMap_unit_d A (Under.mk φ)
    (SimplexCategory.δ (0 : Fin 2)).op X bracket
  have h1 := simplicialModuleMap_unit_d A (Under.mk φ)
    (SimplexCategory.δ (1 : Fin 2)).op X bracket
  rw [h0, h1] at hf
  have e0 := standardMap_face_zero_generator A (Under.mk φ) X x
  have e1 := standardMap_face_one_generator A (Under.mk φ) X x
  erw [e0, e1] at hf
  exact hf.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Homology classes of canonical bracket differentials are additive. -/
theorem homologyZeroGenerator_add {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (b c : B.obj.obj X) :
    homologyZeroGenerator φ X (b + c) =
      homologyZeroGenerator φ X b + homologyZeroGenerator φ X c := by
  let η := (ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).unit.app
      (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom)
  let k : (simplicialModule A (Under.mk φ)).obj (op ⦋0⦌) ⟶ L(φ).homology 0 :=
    (objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ
  let D := (relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).postcomp
    (η ≫ (restrictionAlong (standardAugmentation A (Under.mk φ) (op ⦋0⦌))).map k).val
  let g := CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A (Under.mk φ)
  let ε : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right ⟶ B :=
    standardAugmentation A (Under.mk φ) (op ⦋0⦌)
  have hclass (x : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X) :
      D.d x = homologyZeroGenerator φ X (ε.hom.app X x) :=
    polynomialDifferential_class φ X x
  let y : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X := g.hom.app X b
  let z : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X := g.hom.app X c
  have hb : ε.hom.app X y = b := standardAugmentation_generator φ X b
  have hc : ε.hom.app X z = c := standardAugmentation_generator φ X c
  have hε : ε.hom.app X (y + z) = b + c :=
    ((ε.hom.app X).hom.map_add y z).trans (congrArg₂ (· + ·) hb hc)
  calc
    _ = homologyZeroGenerator φ X (ε.hom.app X (y + z)) :=
      congrArg (homologyZeroGenerator φ X) hε.symm
    _ = D.d (y + z) := (hclass _).symm
    _ = D.d y + D.d z := map_add D.d y z
    _ = _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Homology classes of canonical bracket differentials satisfy the Leibniz identity. -/
theorem homologyZeroGenerator_mul {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (b c : B.obj.obj X) :
    homologyZeroGenerator φ X (b * c) =
      b • homologyZeroGenerator φ X c + c • homologyZeroGenerator φ X b := by
  let η := (ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).unit.app
      (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom)
  let k : (simplicialModule A (Under.mk φ)).obj (op ⦋0⦌) ⟶ L(φ).homology 0 :=
    (objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ
  let D := (relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).postcomp
    (η ≫ (restrictionAlong (standardAugmentation A (Under.mk φ) (op ⦋0⦌))).map k).val
  let g := CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A (Under.mk φ)
  let ε : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right ⟶ B :=
    standardAugmentation A (Under.mk φ) (op ⦋0⦌)
  have hclass (x : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X) :
      D.d x = homologyZeroGenerator φ X (ε.hom.app X x) :=
    polynomialDifferential_class φ X x
  let y : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X := g.hom.app X b
  let z : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X := g.hom.app X c
  have hb : ε.hom.app X y = b := standardAugmentation_generator φ X b
  have hc : ε.hom.app X z = c := standardAugmentation_generator φ X c
  have hε : ε.hom.app X (y * z) = b * c :=
    ((ε.hom.app X).hom.map_mul y z).trans (congrArg₂ (· * ·) hb hc)
  calc
    _ = homologyZeroGenerator φ X (ε.hom.app X (y * z)) :=
      congrArg (homologyZeroGenerator φ X) hε.symm
    _ = D.d (y * z) := (hclass _).symm
    _ = ε.hom.app X y • (show (L(φ).homology 0).val.obj X from D.d z) +
        ε.hom.app X z • (show (L(φ).homology 0).val.obj X from D.d y) := D.d_mul y z
    _ = _ := by rw [hb, hc]; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homology class of a canonical bracket differential vanishes on the base ring sheaf. -/
theorem homologyZeroGenerator_algebraMap {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (a : A.obj.obj X) :
    homologyZeroGenerator φ X (φ.hom.app X a) = 0 := by
  let η := (ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).unit.app
      (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom)
  let k : (simplicialModule A (Under.mk φ)).obj (op ⦋0⦌) ⟶ L(φ).homology 0 :=
    (objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ
  let D := (relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).postcomp
    (η ≫ (restrictionAlong (standardAugmentation A (Under.mk φ) (op ⦋0⦌))).map k).val
  let ε : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right ⟶ B :=
    standardAugmentation A (Under.mk φ) (op ⦋0⦌)
  have hclass (x : (standardTerm A (Under.mk φ) (op ⦋0⦌)).right.obj.obj X) :
      D.d x = homologyZeroGenerator φ X (ε.hom.app X x) :=
    polynomialDifferential_class φ X x
  let x := (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom.hom.app X a
  have hε : ε.hom.app X x = φ.hom.app X a :=
    congrArg (fun k : A ⟶ B => k.hom.app X a)
      (((standardResolution A (Under.mk φ)).hom.app (op ⦋0⦌)).w)
  calc
    _ = homologyZeroGenerator φ X (ε.hom.app X x) :=
      congrArg (homologyZeroGenerator φ X) hε.symm
    _ = D.d x := (hclass _).symm
    _ = 0 := D.d_app a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Homology classes of canonical bracket differentials commute with restriction maps. -/
theorem homologyZeroGenerator_naturality {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (b : B.obj.obj X) :
    homologyZeroGenerator φ Y (B.obj.map f b) =
      (L(φ).homology 0).val.map f (homologyZeroGenerator φ X b) := by
  let η := (ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).unit.app
      (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom)
  let k : (simplicialModule A (Under.mk φ)).obj (op ⦋0⦌) ⟶ L(φ).homology 0 :=
    (objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ
  let D := (relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).postcomp
    (η ≫ (restrictionAlong (standardAugmentation A (Under.mk φ) (op ⦋0⦌))).map k).val
  let γ := (eqToHom (standardResolution_obj_zero A (Under.mk φ)).symm).right
  let g := CategoryTheory.Sheaf.FreeAlgebra.Presentation.generator A (Under.mk φ)
  have hg := g.hom.naturality_apply f b
  have hγ := ConcreteCategory.congr_hom (γ.hom.naturality f) (g.hom.app X b)
  change D.d (γ.hom.app Y (g.hom.app Y (B.obj.map f b))) =
    ((restrictionAlong (standardAugmentation A (Under.mk φ) (op ⦋0⦌))).obj
      (L(φ).homology 0)).val.map f (D.d (γ.hom.app X (g.hom.app X b)))
  exact (congrArg D.d ((congrArg (γ.hom.app Y) hg).trans hγ)).trans (D.d_map f _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homology comparison sends a bracket differential class to the universal differential. -/
theorem homologyZeroMap_generator {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (b : B.obj.obj X) :
    (homologyZeroMap φ).val.app X (homologyZeroGenerator φ X b) =
      (relativeDifferential φ).d b := by
  dsimp only [homologyZeroGenerator]
  change ((objXIso A (Under.mk φ) 0).inv ≫ toHomologyZero φ ≫ homologyZeroMap φ).val.app X _ = _
  erw [toHomologyZero_comp_homologyZeroMap, toKaehler, Iso.inv_hom_id_assoc]
  erw [standardToKaehler_unit_d, standardAugmentation_generator]

/-- The relative derivation sending a section to the homology class of the differential of
its canonical polynomial bracket. -/
def homologyZeroDerivation {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    Der[φ ; L(φ).homology 0] where
  d {X} :=
    { toFun := homologyZeroGenerator φ X
      map_zero' := by
        exact (congrArg (homologyZeroGenerator φ X) (φ.hom.app X).hom.map_zero).symm.trans
          (homologyZeroGenerator_algebraMap φ X 0)
      map_add' := homologyZeroGenerator_add φ X }
  d_mul {X} := homologyZeroGenerator_mul φ X
  d_map := homologyZeroGenerator_naturality φ
  d_app {X} := homologyZeroGenerator_algebraMap φ X

/-- The morphism from relative differentials to zeroth homology induced by the canonical
bracket differential classes. -/
def homologyZeroInv {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    Ω(φ) ⟶ L(φ).homology 0 :=
  relativeDifferentialDesc φ (homologyZeroDerivation φ)

/-- The inverse comparison sends a universal differential to its canonical bracket class. -/
theorem homologyZeroInv_d {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (b : B.obj.obj X) :
    (homologyZeroInv φ).val.app X (((relativeDifferential φ).app X).d b) =
      homologyZeroGenerator φ X b := by
  exact RelativeDifferentials.homEquiv_symm_apply_d φ (homologyZeroDerivation φ) X b

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation comparison followed by the bracket-class comparison is the identity
on zeroth homology. -/
theorem homologyZeroMap_comp_inv {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    homologyZeroMap φ ≫ homologyZeroInv φ = 𝟙 _ := by
  letI := toHomologyZero_epi φ
  apply (cancel_epi (toHomologyZero φ)).mp
  erw [← Category.assoc, toHomologyZero_comp_homologyZeroMap, Category.comp_id]
  apply (cancel_epi (objXIso A (Under.mk φ) 0).inv).mp
  simp only [toKaehler, Category.assoc, Iso.inv_hom_id_assoc]
  let adj := ChangeOfRings.extendRestrictAdjunction
    (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))
  apply (adj.homEquiv _ _).injective
  apply relativeDifferential_postcomp_injective (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom
  ext X x
  change (homologyZeroInv φ).val.app X
      ((standardToKaehler φ).val.app X
        ((adj.unit.app _).val.app X
          ((relativeDifferential (standardTerm A (Under.mk φ) (op ⦋0⦌)).hom).d x))) = _
  erw [standardToKaehler_unit_d, homologyZeroInv_d]
  exact (polynomialDifferential_class φ X x).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bracket-class comparison followed by the augmentation comparison is the identity
on relative differentials. -/
theorem homologyZeroInv_comp_map {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    homologyZeroInv φ ≫ homologyZeroMap φ = 𝟙 _ := by
  apply relativeDifferential_postcomp_injective φ
  ext X b
  change (homologyZeroMap φ).val.app X
    ((homologyZeroInv φ).val.app X ((relativeDifferential φ).d b)) = (relativeDifferential φ).d b
  erw [homologyZeroInv_d, homologyZeroMap_generator]

/-- The canonical augmentation comparison on zeroth homology is an isomorphism. -/
instance homologyZeroMap_isIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    IsIso (homologyZeroMap φ) :=
  ⟨⟨homologyZeroInv φ, homologyZeroMap_comp_inv φ, homologyZeroInv_comp_map φ⟩⟩

/-- Zeroth cohomology of the standard-resolution cotangent complex is canonically isomorphic
to the sheaf of relative Kähler differentials. -/
def homologyZeroIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).homology 0 ≅ Ω(φ) where
  hom := homologyZeroMap φ
  inv := homologyZeroInv φ
  hom_inv_id := homologyZeroMap_comp_inv φ
  inv_hom_id := homologyZeroInv_comp_map φ

/-- The forward morphism of the zeroth-homology isomorphism is the augmentation comparison. -/
theorem homologyZeroIso_hom {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (homologyZeroIso φ).hom = homologyZeroMap φ :=
  rfl

/-- The inverse morphism of the zeroth-homology isomorphism is the categorical inverse of
the augmentation comparison. -/
theorem homologyZeroIso_inv {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (homologyZeroIso φ).inv = inv (homologyZeroMap φ) := by
  exact IsIso.eq_inv_of_hom_inv_id (homologyZeroMap_comp_inv φ)

end SheafOfModules.RingedSite.CotangentComplex
