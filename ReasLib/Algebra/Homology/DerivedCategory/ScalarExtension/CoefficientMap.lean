/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive

/-! # Coefficient maps between termwise scalar extensions -/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- The coefficient-change map on termwise scalar extensions is the extension–restriction
unit followed by the scalar-extension composition identification. -/
def cochainScalarExtensionMap (σ : R →+* A) (τ : A →+* B) (ρ : R →+* B)
    (hcomp : τ.comp σ = ρ) (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)).obj M ⟶
      ((ModuleCat.restrictScalars τ).mapHomologicalComplex (up ℤ)).obj
        (((ModuleCat.extendScalars ρ).mapHomologicalComplex (up ℤ)).obj M) :=
  (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} A) (up ℤ)).inv.app
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)).obj M) ≫
    (NatTrans.mapHomologicalComplex (ModuleCat.extendRestrictScalarsAdj τ).unit (up ℤ)).app
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)).obj M) ≫
    ((ModuleCat.restrictScalars τ).mapHomologicalComplex (up ℤ)).map
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp σ τ) (up ℤ)).inv.app M ≫
        eqToHom (congrArg
          (fun χ : R →+* B ↦ ((ModuleCat.extendScalars χ).mapHomologicalComplex (up ℤ)).obj M)
          hcomp))

/-- Localization of the termwise coefficient map, with exact scalar restriction in the
target derived category. -/
def derivedCochainScalarExtensionMap (σ : R →+* A) (τ : A →+* B) (ρ : R →+* B)
    (hcomp : τ.comp σ = ρ) (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj (((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)).obj M) ⟶
      (derivedRestrictionOfScalars τ).obj
        (DerivedCategory.Q.obj (((ModuleCat.extendScalars ρ).mapHomologicalComplex (up ℤ)).obj M)) :=
  DerivedCategory.Q.map (cochainScalarExtensionMap σ τ ρ hcomp M) ≫
    (ModuleCat.restrictScalars τ).mapDerivedCategoryFactors.inv.app
      (((ModuleCat.extendScalars ρ).mapHomologicalComplex (up ℤ)).obj M)

/-- The derived coefficient map is localization of the cochain map followed by the
canonical exact-restriction comparison. -/
theorem derivedCochainScalarExtensionMap_eq
    (σ : R →+* A) (τ : A →+* B) (ρ : R →+* B)
    (hcomp : τ.comp σ = ρ) (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    derivedCochainScalarExtensionMap σ τ ρ hcomp M =
      DerivedCategory.Q.map (cochainScalarExtensionMap σ τ ρ hcomp M) ≫
        (ModuleCat.restrictScalars τ).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.extendScalars ρ).mapHomologicalComplex (up ℤ)).obj M) := rfl

end CategoryTheory.ModuleCat
