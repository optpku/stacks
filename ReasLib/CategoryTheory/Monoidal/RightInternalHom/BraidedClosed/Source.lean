/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Source
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Enrichment

/-!
# Comparing right internal Homs with source-order closed maps

The canonical right internal-Hom structure obtained from a braided closed category recovers the
source-order tensor and coevaluation maps.  Composition and the iterated internal-Hom map use the
opposite crossing convention, so their comparison with the chosen source-order owners requires a
symmetric braiding.  These bridges let downstream code move between the bundled right-oriented API
and the canonical `MonoidalClosed` owners without unfolding either construction.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

set_option backward.isDefEq.respectTransparency false

namespace RightInternalHom.ofBraidedClosed

section Symmetric

variable [SymmetricCategory C]

/-- Composition for the canonical right internal Hom is source-order closed composition. -/
theorem comp (X Y Z : C) :
    (RightInternalHom.ofBraidedClosed (C := C)).comp X Y Z =
      MonoidalClosed.Source.comp X Y Z := by
  apply (RightInternalHom.ofBraidedClosed (C := C)).uncurry_injective
  rw [RightInternalHom.uncurry_comp]
  rw [RightInternalHom.ofBraidedClosed.uncurry]
  simp only [MonoidalClosed.Source.comp]
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.comp_eq,
    MonoidalClosed.uncurry_curry]
  rw [RightInternalHom.ofBraidedClosed.ev,
    RightInternalHom.ofBraidedClosed.ev]
  change
    (α_ ((ihom Y).obj Z) ((ihom X).obj Y) X).hom ≫
          ((ihom Y).obj Z ◁ ((β_ X ((ihom X).obj Y)).inv ≫
            (ihom.ev X).app Y)) ≫
          (β_ Y ((ihom Y).obj Z)).inv ≫ (ihom.ev Y).app Z =
      (β_ X ((ihom Y).obj Z ⊗ (ihom X).obj Y)).inv ≫
        (X ◁ (β_ ((ihom Y).obj Z) ((ihom X).obj Y)).hom) ≫
        MonoidalClosed.compTranspose X Y Z
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  rw [MonoidalClosed.compTranspose_eq]
  slice_lhs 3 4 =>
    exact BraidedCategory.braiding_inv_naturality_right
      ((ihom Y).obj Z) ((ihom.ev X).app Y)
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding
    ((ihom X).obj Y) ((ihom Y).obj Z)]
  change
    (α_ ((ihom Y).obj Z) ((ihom X).obj Y) X).hom ≫
        ((ihom Y).obj Z ◁ (β_ X ((ihom X).obj Y)).inv) ≫
        ((β_ (X ⊗ (ihom X).obj Y) ((ihom Y).obj Z)).inv ≫
          ((ihom.ev X).app Y ▷ (ihom Y).obj Z)) ≫
        (ihom.ev Y).app Z =
      (β_ X ((ihom Y).obj Z ⊗ (ihom X).obj Y)).inv ≫
        (X ◁ (β_ ((ihom X).obj Y) ((ihom Y).obj Z)).inv) ≫
        (α_ X ((ihom X).obj Y) ((ihom Y).obj Z)).inv ≫
        ((ihom.ev X).app Y ▷ (ihom Y).obj Z) ≫ (ihom.ev Y).app Z
  rw [BraidedCategory.braiding_tensor_left_inv_assoc,
    BraidedCategory.braiding_tensor_right_inv_assoc]
  simp only [Category.assoc]

end Symmetric

section Braided

variable [BraidedCategory C]

/-- Left tensoring for the canonical right internal Hom is the source-order tensor/internal-Hom
comparison. -/
theorem tensorLeft (X Y Z : C) :
    (RightInternalHom.ofBraidedClosed (C := C)).tensorLeft X Y Z =
      MonoidalClosed.Source.tensor Z Y X := by
  apply (RightInternalHom.ofBraidedClosed (C := C)).uncurry_injective
  rw [RightInternalHom.uncurry_tensorLeft]
  rw [RightInternalHom.ofBraidedClosed.uncurry]
  rw [MonoidalClosed.Source.tensor_spec]
  rw [RightInternalHom.ofBraidedClosed.ev]
  change
    (α_ Z ((ihom X).obj Y) X).hom ≫
        (Z ◁ ((β_ X ((ihom X).obj Y)).inv ≫ (ihom.ev X).app Y)) =
      (β_ X (Z ⊗ (ihom X).obj Y)).inv ≫
        (α_ X Z ((ihom X).obj Y)).inv ≫
        ((β_ X Z).hom ▷ (ihom X).obj Y) ≫
        (α_ Z X ((ihom X).obj Y)).hom ≫ Z ◁ (ihom.ev X).app Y
  rw [MonoidalCategory.whiskerLeft_comp,
    BraidedCategory.braiding_tensor_right_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  simp

/-- Coevaluation for the canonical right internal Hom is the standard tensor/internal-Hom unit. -/
theorem coev_eq_tensorInternalHomUnit (X Y : C) :
    (RightInternalHom.ofBraidedClosed (C := C)).coev X Y =
      MonoidalClosed.tensorInternalHomUnit Y X := by
  rw [RightInternalHom.ofBraidedClosed.coev,
    MonoidalClosed.tensorInternalHomUnit_spec]

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- The braided composition transpose for the canonical right internal Hom is the canonical
source-order map into an iterated internal Hom. -/
theorem compTranspose (X Y Z : C) :
    (RightInternalHom.ofBraidedClosed (C := C)).compTranspose X Y Z =
      MonoidalClosed.Source.Iterated.map X Y Z := by
  apply (RightInternalHom.ofBraidedClosed (C := C)).uncurry_injective
  rw [RightInternalHom.uncurry_compTranspose]
  rw [RightInternalHom.ofBraidedClosed.uncurry]
  change
    (α_ ((ihom Y).obj Z) X ((ihom X).obj Y)).hom ≫
        ((ihom Y).obj Z ◁ (β_ X ((ihom X).obj Y)).hom) ≫
        ((ihom Y).obj Z ◁
          (RightInternalHom.ofBraidedClosed (C := C)).ev X Y) ≫
        (RightInternalHom.ofBraidedClosed (C := C)).ev Y Z =
      (β_ ((ihom X).obj Y) ((ihom Y).obj Z ⊗ X)).inv ≫
        MonoidalClosed.uncurry (MonoidalClosed.Source.Iterated.map X Y Z)
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding
    ((ihom X).obj Y) ((ihom Y).obj Z ⊗ X)]
  rw [← MonoidalClosed.braidedHomEquiv_symm_apply]
  rw [MonoidalClosed.Source.Iterated.map_spec]
  simp only [MonoidalClosed.Source.Iterated.side]
  rw [← RightInternalHom.ofBraidedClosed.comp]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding
    X ((ihom X).obj Z)]
  rw [← RightInternalHom.ofBraidedClosed.uncurry]
  have hid :
      (RightInternalHom.ofBraidedClosed (C := C)).uncurry
          (𝟙 ((ihom X).obj Z)) =
        (RightInternalHom.ofBraidedClosed (C := C)).ev X Z :=
    (RightInternalHom.ofBraidedClosed (C := C)).uncurry_id_eq_ev X Z
  rw [hid]
  have hcomp :
      (RightInternalHom.ofBraidedClosed (C := C)).comp X Y Z ▷ X ≫
          (RightInternalHom.ofBraidedClosed (C := C)).ev X Z =
        (RightInternalHom.ofBraidedClosed (C := C)).uncurry
          ((RightInternalHom.ofBraidedClosed (C := C)).comp X Y Z) :=
    ((RightInternalHom.ofBraidedClosed (C := C)).uncurry_eq
      ((RightInternalHom.ofBraidedClosed (C := C)).comp X Y Z)).symm
  rw [hcomp]
  rw [RightInternalHom.uncurry_comp]
  change
    (α_ ((ihom Y).obj Z) X ((ihom X).obj Y)).hom ≫
        ((ihom Y).obj Z ◁ (β_ X ((ihom X).obj Y)).hom) ≫
        ((ihom Y).obj Z ◁
          (RightInternalHom.ofBraidedClosed (C := C)).ev X Y) ≫
        (RightInternalHom.ofBraidedClosed (C := C)).ev Y Z =
      (β_ ((ihom Y).obj Z ⊗ X) ((ihom X).obj Y)).hom ≫
        (α_ ((ihom X).obj Y) ((ihom Y).obj Z) X).inv ≫
        ((β_ ((ihom X).obj Y) ((ihom Y).obj Z)).hom ▷ X) ≫
        (α_ ((ihom Y).obj Z) ((ihom X).obj Y) X).hom ≫
        ((ihom Y).obj Z ◁
          (RightInternalHom.ofBraidedClosed (C := C)).ev X Y) ≫
        (RightInternalHom.ofBraidedClosed (C := C)).ev Y Z
  rw [BraidedCategory.braiding_tensor_left_hom_assoc]
  simp only [Iso.hom_inv_id_assoc]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding
    ((ihom Y).obj Z) ((ihom X).obj Y)]
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  simp

end Symmetric

end RightInternalHom.ofBraidedClosed

end CategoryTheory
