/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteQuotientCoefficientResolution
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientAssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
noncomputable section
universe u

namespace FiniteAssociatedResolution
variable {X : Scheme.{u}} (R : Type (u + 1)) [Ring R] [Finite R]
variable [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable (M : (finiteTypeDiscreteModule R (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar))).FullSubcategory)

/-- The explicit finite-quotient free resolution, realized by the actual germ-based sheaf functor. -/
def complex := ((functor (Λ := R) (xbar := xbar)).mapHomologicalComplex
  (ComplexShape.down ℕ)).obj
    (FiniteQuotientCoefficientResolution.complex R (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) M.obj)

/-- Augmentation to the published finite inverse, using the specified finite-stage comparison. -/
def augmentation : complex R xbar M ⟶ (ChainComplex.single₀ _).obj
    ((associatedSheafFunctor R xbar).obj M) :=
  ((functor (Λ := R) (xbar := xbar)).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (FiniteQuotientCoefficientResolution.augmentation R (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber xbar)) M.obj) ≫
  ((HomologicalComplex.singleMapHomologicalComplex (functor (Λ := R) (xbar := xbar))
    (ComplexShape.down ℕ) 0).app M.obj).hom ≫
  (ChainComplex.single₀ _).map (finiteComparison M)

/-- Exactness can be checked on the actual stalk comparisons; no finite-category
projectivity or arbitrary resolution comparison is used. -/
theorem augmentation_quasiIso : QuasiIso (augmentation R xbar M) := by sorry

variable {Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R,
  (etaleRestriction j).op.HasLeftKanExtension F]

/-- Extension by zero between module sheaves preserves addition of morphisms. -/
instance extension_additive : (etaleExtensionByZero j (ModuleCat.{u + 1} R)).Additive := by sorry

/-- Apply actual extension by zero to the finite locally projective resolution. -/
def compactComplex := ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).mapHomologicalComplex
  (ComplexShape.down ℕ)).obj (complex R xbar M)

/-- The compact-support augmentation retains the specified map and its coefficient sheaf. -/
def compactAugmentation : compactComplex R xbar M j ⟶ (ChainComplex.single₀ _).obj
    ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).obj ((associatedSheafFunctor R xbar).obj M)) :=
  ((etaleExtensionByZero j (ModuleCat.{u + 1} R)).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (augmentation R xbar M) ≫
  ((HomologicalComplex.singleMapHomologicalComplex (etaleExtensionByZero j (ModuleCat.{u + 1} R))
    (ComplexShape.down ℕ) 0).app ((associatedSheafFunctor R xbar).obj M)).hom

/-- Extension by zero is exact for the stated open immersion. -/
theorem compactAugmentation_quasiIso : QuasiIso (compactAugmentation R xbar M j) := by sorry

end FiniteAssociatedResolution
