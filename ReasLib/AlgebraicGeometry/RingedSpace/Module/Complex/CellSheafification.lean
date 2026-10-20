/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CellReplacement
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Sheafification of the displayed cell replacement

The input complex is retained. The actual presheaf augmentation is transported
through the explicit sheafification adjunction, degree by degree. No new
representative or quasi-isomorphism is selected from an existence theorem.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u

namespace AlgebraicGeometry.RingedSpace.CellReplacement

variable {X : RingedSpace.{u}} (K : CochainComplex X.Modules ℤ)

def underlying : CochainComplex (PresheafOfModules.{u} X.ringCatSheaf.obj) ℤ :=
  ((SheafOfModules.forget X.ringCatSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

def presheafModel : CochainComplex (PresheafOfModules.{u} X.ringCatSheaf.obj) ℤ :=
  PresheafOfModules.CellReplacement.replacement (underlying K)

def presheafAugmentation : presheafModel K ⟶ underlying K :=
  PresheafOfModules.CellReplacement.augmentation (underlying K)

/-- The actual terms obtained by sheafifying the explicit free-cell tower. -/
def modelTerm (n : ℤ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj ((presheafModel K).X n)

def modelDifferential (n : ℤ) : modelTerm K n ⟶ modelTerm K (n + 1) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ((presheafModel K).d n (n + 1))

theorem modelDifferential_sq (n : ℤ) :
    modelDifferential K n ≫ modelDifferential K (n + 1) = 0 := by
  sorry

/-- The actual global sheaf complex underlying the replacement. -/
def model : CochainComplex X.Modules ℤ :=
  CochainComplex.of (modelTerm K) (modelDifferential K) (modelDifferential_sq K)

/-- Each augmentation component is the canonical adjoint of the original
presheaf comparison, with no existence-based selection. -/
def augmentationTerm (n : ℤ) : modelTerm K n ⟶ K.X n :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    ((presheafModel K).X n) (K.X n)).symm ((presheafAugmentation K).f n)

def augmentation : model K ⟶ K where
  f := augmentationTerm K
  comm' := by sorry

/-- Exact sheafification carries the actual presheaf cell-resolution
augmentation to a quasi-isomorphism of sheaf complexes. -/
theorem augmentation_quasiIso : QuasiIso (augmentation K) := by
  sorry

/-- The adjunction recovers exactly the specified original presheaf map. -/
theorem augmentationTerm_adjoint (n : ℤ) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      ((presheafModel K).X n) (K.X n) (augmentationTerm K n) =
      (presheafAugmentation K).f n :=
  Equiv.apply_symm_apply _ _

/-- The image of the actual augmentation is the comparison isomorphism in
the standard derived category; its forward map is fixed, not selected. -/
def comparison : (DerivedCategory.Q (C := X.Modules)).obj (model K) ≅
    (DerivedCategory.Q (C := X.Modules)).obj K := by
  letI : QuasiIso (augmentation K) := augmentation_quasiIso K
  exact asIso ((DerivedCategory.Q (C := X.Modules)).map (augmentation K))

theorem comparison_hom : (comparison K).hom =
    (DerivedCategory.Q (C := X.Modules)).map (augmentation K) := rfl

end AlgebraicGeometry.RingedSpace.CellReplacement
