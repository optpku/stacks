/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.OpenQuotientInflation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGroupAlgebraModule

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace FiniteQuotientCoefficientResolution
variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : DiscreteModuleCat R G) [Finite M.obj.V]

/-- The single actual finite coefficient action kernel. -/
abbrev kernel := FiniteComplexQuotient.normalKernel R G M

/-- Its quotient embeds in the finite automorphism group of M. -/
instance quotient_finite : Finite (G ⧸ (kernel R G M).toSubgroup) := by sorry

/-- The specified descended action of this finite quotient. -/
def quotientAction : Action (ModuleCat.{max u v} R) (G ⧸ (kernel R G M).toSubgroup) where
  V := M.obj.V
  ρ := QuotientGroup.lift (kernel R G M).toSubgroup M.obj.ρ (fun _ h ↦ h)

/-- The actual group-algebra coefficient module. -/
abbrev coefficient := (NoncommGroupAlgebraModule.toFunctor R
  (G ⧸ (kernel R G M).toSubgroup)).obj (quotientAction R G M)

/-- Recover G-action by restriction from the group algebra, then inflation.
This exact functor is NOT asserted to preserve projectivity in all discrete G-modules. -/
def realization := NoncommGroupAlgebraModule.fromFunctor R (G ⧸ (kernel R G M).toSubgroup) ⋙
  OpenQuotientInflation.functor R G (kernel R G M)

instance realization_additive : (realization R G M).Additive := by sorry
instance realization_preservesHomology : (realization R G M).PreservesHomology := by sorry

/-- Inflation of the specified quotient representation is identity on the given vectors. -/
def quotientIso :
    (OpenQuotientInflation.functor R G (kernel R G M)).obj (quotientAction R G M) ≅ M :=
  ObjectProperty.isoMk _ (Action.mkIso (Iso.refl M.obj.V) (fun _ ↦ by sorry))

/-- The explicit group-algebra recovery followed by that identity inflation map. -/
def coefficientIso : (realization R G M).obj (coefficient R G M) ≅ M :=
  (OpenQuotientInflation.functor R G (kernel R G M)).mapIso
    (NoncommGroupAlgebraModule.actionIso R (G ⧸ (kernel R G M).toSubgroup) (quotientAction R G M)) ≪≫
    quotientIso R G M

/-- The fixed kernel/free resolution over the ACTUAL finite quotient algebra. -/
abbrev algebraResolution := FiniteFreeModuleResolution.resolution
  (MonoidAlgebra R (G ⧸ (kernel R G M).toSubgroup)) (coefficient R G M)

/-- Inflate that actual resolution as a continuous G-complex. -/
def complex := ((realization R G M).mapHomologicalComplex (ComplexShape.down ℕ)).obj
  (algebraResolution R G M).complex

/-- Actual augmentation, with the standard single-complex compositor and the specified recovery map. -/
def augmentation : complex R G M ⟶ (ChainComplex.single₀ _).obj M :=
  ((realization R G M).mapHomologicalComplex (ComplexShape.down ℕ)).map (algebraResolution R G M).π ≫
    ((HomologicalComplex.singleMapHomologicalComplex (realization R G M) (ComplexShape.down ℕ) 0).app
      (coefficient R G M)).hom ≫
    (ChainComplex.single₀ _).map (coefficientIso R G M).hom

/-- Exact inflation preserves this specified augmentation's quasi-isomorphism. -/
theorem augmentation_quasiIso : QuasiIso (augmentation R G M) := by sorry

/-- Terms are projective over the COEFFICIENT ring R because the group algebra
is free over R. No projectivity after inflation to continuous G-modules is claimed. -/
theorem term_coefficient_projective (n : ℕ) : Module.Projective R ((complex R G M).X n).obj.V := by sorry

/-- Finite R and the genuine finite quotient give finite terms of this actual construction. -/
theorem term_finite [Finite R] (n : ℕ) : Finite ((complex R G M).X n).obj.V := by sorry

end FiniteQuotientCoefficientResolution
