/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GlobalEtaObject

/-!
# The actual original-input comparison and the global eta specification

The comparison is the total-left-derived counit on the displayed cell model,
followed by the existing canonical homotopy-to-complex localization factor.
Its inverse is only taken after the fixed-map K-flat computation certificate.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.PerfectGraphAtlas

variable {X Y : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace)
  (hE : RingedSpace.ModuleDerived.IsPerfect E) (p : Y ⟶ X) (D : Y.IdealSheafData)
  [IsEffectiveCartierDivisor D.subschemeι]

def graphCellHomotopy : HomotopyCategory X.toRingedSpace.Modules (ComplexShape.up ℤ) :=
  (HomotopyCategory.quotient _ _).obj (originalCellModel E hE)

/-- The fixed derived counit at the explicit cell model, retaining the exact
underived pullback along b≫p. -/
def graphCellCounit :
    (RingedSpace.modulePullbackDerived (globalB E hE p D ≫ p).toShHom).obj
      (DerivedCategory.Qh.obj (graphCellHomotopy E hE)) ⟶
    (RingedSpace.modulePullbackToDerived (globalB E hE p D ≫ p).toShHom).obj
      (graphCellHomotopy E hE) :=
  ((RingedSpace.modulePullbackToDerived (globalB E hE p D ≫ p).toShHom).totalLeftDerivedCounit
    DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)).app (graphCellHomotopy E hE)

/-- The free-cell filtration is K-flat, and its sheaf terms have flat stalks.
It therefore computes the actual total-left-derived pullback at this model. -/
theorem graphCellCounit_isIso : IsIso (graphCellCounit E hE p D) := by
  sorry

def graphCellCounitIso :
    (RingedSpace.modulePullbackDerived (globalB E hE p D ≫ p).toShHom).obj
      (DerivedCategory.Qh.obj (graphCellHomotopy E hE)) ≅
    (RingedSpace.modulePullbackToDerived (globalB E hE p D ≫ p).toShHom).obj
      (graphCellHomotopy E hE) :=
  @asIso _ _ _ _ (graphCellCounit E hE p D) (graphCellCounit_isIso E hE p D)

/-- Canonical localization comparison, built from Mathlib's actual factor maps. -/
def graphCellLocalizationIso :
    (RingedSpace.modulePullbackToDerived (globalB E hE p D ≫ p).toShHom).obj
      (graphCellHomotopy E hE) ≅
    (DerivedCategory.Q (C := (globalW E hE p D).toRingedSpace.Modules)).obj (graphCellModel E hE p D) :=
  DerivedCategory.Qh.mapIso
    (((graphModulePullback E hE p D).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
      (originalCellModel E hE)) ≪≫
    (DerivedCategory.quotientCompQhIso (globalW E hE p D).toRingedSpace.Modules).app (graphCellModel E hE p D)

/-- The complete actual comparison from pullback of the original E to the
localization of the specific pulled-back cell complex. -/
def graphCellDerivedComparison :
    (RingedSpace.modulePullbackDerived (globalB E hE p D ≫ p).toShHom).obj E ≅
      (DerivedCategory.Q (C := (globalW E hE p D).toRingedSpace.Modules)).obj (graphCellModel E hE p D) :=
  (RingedSpace.modulePullbackDerived (globalB E hE p D ≫ p).toShHom).mapIso
    ((originalCellComparison E hE).symm ≪≫
      ((DerivedCategory.quotientCompQhIso X.toRingedSpace.Modules).app (originalCellModel E hE)).symm) ≪≫
    graphCellCounitIso E hE p D ≪≫ graphCellLocalizationIso E hE p D

theorem graphCellCounitIso_hom :
    (graphCellCounitIso E hE p D).hom = graphCellCounit E hE p D := rfl

/-- Eta of the actual cell model is perfect after the prescribed product-ideal
modification. On every good affine chart this is the source's finite locally
free eta complex, with the original derived comparison preserved. -/
theorem globalQ_isPerfect : RingedSpace.ModuleDerived.IsPerfect (globalQ E hE p D) := by
  sorry

/-- On the fixed good chart of W, the constructed global Q has the actual
local eta model previously used to define its decomposition ideal. No local
or global Q is selected from this proposition. -/
theorem globalQ_local (i : GoodEtaChart E hE p D) :
    IsIsomorphic
      ((RingedSpace.moduleDerivedSectionsAtOpen (globalW E hE p D).toRingedSpace i.1.U).obj
        (globalQ E hE p D))
      (etaChartQ E hE p D i) := by
  sorry

end AlgebraicGeometry.Scheme.PerfectGraphAtlas
