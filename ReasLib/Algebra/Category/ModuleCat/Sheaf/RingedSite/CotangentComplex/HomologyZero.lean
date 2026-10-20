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

/-- The Kähler base-change map `Ω_{P_0/A} ⊗_{P_0} B ⟶ Ω(φ)` along the standard-resolution
augmentation. -/
def standardToKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (simplicialModule A (Under.mk φ)).obj (op ⦋0⦌) ⟶ Ω(φ) :=
  ((ChangeOfRings.extendRestrictAdjunction
      (ringSheafMap (standardAugmentation A (Under.mk φ) (op ⦋0⦌)))).homEquiv _ _).symm
    (RelativeDifferentials.map
      ⟨standardAugmentation_w A (Under.mk φ) (op ⦋0⦌)⟩)

/-- The degree-zero component of the canonical cochain comparison `L(φ) ⟶ Ω(φ)[0]`, obtained by
transporting Kähler base change of the standard-resolution augmentation along `objXIso`. -/
def toKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ).X 0 ⟶ Ω(φ) :=
  (objXIso A (Under.mk φ) 0).hom ≫ standardToKaehler φ

/-- The incoming differential of `L(φ)` into degree zero followed by `toKaehler` is zero. -/
theorem d_comp_toKaehler {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (i : ℤ) (h : (ComplexShape.up ℤ).Rel i 0) :
    L(φ).d i 0 ≫ toKaehler φ = 0 :=
  sorry

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

/-- Homology classes of canonical bracket differentials are additive. -/
theorem homologyZeroGenerator_add {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (b c : B.obj.obj X) :
    homologyZeroGenerator φ X (b + c) =
      homologyZeroGenerator φ X b + homologyZeroGenerator φ X c :=
  sorry

/-- Homology classes of canonical bracket differentials satisfy the Leibniz identity. -/
theorem homologyZeroGenerator_mul {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (b c : B.obj.obj X) :
    homologyZeroGenerator φ X (b * c) =
      b • homologyZeroGenerator φ X c + c • homologyZeroGenerator φ X b :=
  sorry

/-- The homology class of a canonical bracket differential vanishes on the base ring sheaf. -/
theorem homologyZeroGenerator_algebraMap {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (X : Cᵒᵖ) (a : A.obj.obj X) :
    homologyZeroGenerator φ X (φ.hom.app X a) = 0 :=
  sorry

/-- Homology classes of canonical bracket differentials commute with restriction maps. -/
theorem homologyZeroGenerator_naturality {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (b : B.obj.obj X) :
    homologyZeroGenerator φ Y (B.obj.map f b) =
      (L(φ).homology 0).val.map f (homologyZeroGenerator φ X b) :=
  sorry

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

/-- The augmentation comparison followed by the bracket-class comparison is the identity
on zeroth homology. -/
theorem homologyZeroMap_comp_inv {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    homologyZeroMap φ ≫ homologyZeroInv φ = 𝟙 _ :=
  sorry

/-- The bracket-class comparison followed by the augmentation comparison is the identity
on relative differentials. -/
theorem homologyZeroInv_comp_map {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    homologyZeroInv φ ≫ homologyZeroMap φ = 𝟙 _ :=
  sorry

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
