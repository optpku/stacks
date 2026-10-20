/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RootsModuleSheaf

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace OpenExtensionInjectiveResolution
variable {X Y : Scheme.{u}} (R : Type (u + 1)) [Ring R]
variable (j : X ⟶ Y) [IsOpenImmersion j]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))]

instance restriction_additive : (etaleRestrictionSheaf j (ModuleCat.{u + 1} R)).Additive := by sorry

variable (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- Resolve the actual extension by zero, not an invented compactification coefficient. -/
abbrev compactResolution := injectiveResolution ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).obj F)

/-- Termwise restriction of that SAME compactification resolution. -/
def cocomplex := ((etaleRestrictionSheaf j (ModuleCat.{u + 1} R)).mapHomologicalComplex
  (ComplexShape.up ℕ)).obj (compactResolution R j F).cocomplex

/-- The augmentation is the actual j!-restriction unit followed by the restricted resolution map. -/
def augmentation : (CochainComplex.single₀ _).obj F ⟶ cocomplex R j F :=
  (CochainComplex.single₀ _).map
    ((etaleExtensionByZero_adjunction j (ModuleCat.{u + 1} R)).unit.app F) ≫
  ((HomologicalComplex.singleMapHomologicalComplex (etaleRestrictionSheaf j (ModuleCat.{u + 1} R))
    (ComplexShape.up ℕ) 0).app ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).obj F)).inv ≫
  ((etaleRestrictionSheaf j (ModuleCat.{u + 1} R)).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (compactResolution R j F).ι

/-- Restriction preserves injectives because its left adjoint j! is exact. -/
theorem term_injective (n : ℕ) : Injective ((cocomplex R j F).X n) := by sorry

/-- Restriction is exact and the actual j!-restriction unit is invertible. -/
theorem augmentation_quasiIso : QuasiIso (augmentation R j F) := by sorry

/-- An actual injective resolution ON X. No assertion of concentration of Rj_*
on Y is made or used. -/
def resolution : InjectiveResolution F where
  cocomplex := cocomplex R j F
  injective := term_injective R j F
  ι := augmentation R j F
  quasiIso := augmentation_quasiIso R j F

variable [EnoughInjectives (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))]

/-- Specified comparison with the existing arithmetic injective resolution:
both arrows are the recursive injective-extension construction, with its homotopies. -/
def comparison := InjectiveResolution.homotopyEquiv (resolution R j F) (injectiveResolution F)

/-- This comparison respects the actual augmentation, not just cohomology objects. -/
theorem comparison_augmentation : augmentation R j F ≫ (comparison R j F).hom =
    (injectiveResolution F).ι :=
  InjectiveResolution.homotopyEquiv_hom_ι (resolution R j F) (injectiveResolution F)

end OpenExtensionInjectiveResolution
