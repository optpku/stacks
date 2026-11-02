/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.OpenQuotientInflation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGroupAlgebraModule
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

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
instance quotient_finite : Finite (G ⧸ (kernel R G M).toSubgroup) := by
  letI : Finite (End M.obj.V) :=
    Finite.of_injective (fun f : End M.obj.V ↦ (f.hom : M.obj.V → M.obj.V))
      (fun _ _ h ↦ ModuleCat.hom_ext (DFunLike.coe_injective h))
  exact Finite.of_injective
    (QuotientGroup.lift (kernel R G M).toSubgroup M.obj.ρ (fun _ h ↦ h))
    ((QuotientGroup.injective_lift_iff _ _ _).2 rfl)

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

instance realization_additive : (realization R G M).Additive := by
  dsimp only [realization]
  infer_instance
instance realization_preservesHomology : (realization R G M).PreservesHomology := by
  let F := NoncommGroupAlgebraModule.fromFunctor R (G ⧸ (kernel R G M).toSubgroup)
  let H := OpenQuotientInflation.functor R G (kernel R G M)
  letI := Functor.preservesFiniteLimits_of_preservesHomology F
  letI := Functor.preservesFiniteColimits_of_preservesHomology F
  letI := Functor.preservesFiniteLimits_of_preservesHomology H
  letI := Functor.preservesFiniteColimits_of_preservesHomology H
  change (F ⋙ H).PreservesHomology
  infer_instance

/-- Inflation of the specified quotient representation is identity on the given vectors. -/
def quotientIso :
    (OpenQuotientInflation.functor R G (kernel R G M)).obj (quotientAction R G M) ≅ M :=
  ObjectProperty.isoMk _ (Action.mkIso (Iso.refl M.obj.V) (fun g ↦ by
    change (quotientAction R G M).ρ (QuotientGroup.mk' (kernel R G M).toSubgroup g) ≫
      𝟙 M.obj.V = 𝟙 M.obj.V ≫ M.obj.ρ g
    simp only [Category.id_comp]
    rfl))

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
theorem augmentation_quasiIso : QuasiIso (augmentation R G M) := by
  letI : QuasiIso (algebraResolution R G M).π := (algebraResolution R G M).quasiIso
  letI : QuasiIso (((realization R G M).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (algebraResolution R G M).π) := inferInstance
  let e := ((HomologicalComplex.singleMapHomologicalComplex (realization R G M)
    (ComplexShape.down ℕ) 0).app (coefficient R G M)) ≪≫
    (ChainComplex.single₀ _).mapIso (coefficientIso R G M)
  change QuasiIso (((realization R G M).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (algebraResolution R G M).π ≫ e.hom)
  exact quasiIso_comp _ _

/-- Terms are projective over the COEFFICIENT ring R because the group algebra
is free over R. No projectivity after inflation to continuous G-modules is claimed. -/
theorem term_coefficient_projective (n : ℕ) : Module.Projective R ((complex R G M).X n).obj.V := by
  let Q := G ⧸ (kernel R G M).toSubgroup
  let A := MonoidAlgebra R Q
  let T := FiniteFreeModuleResolution.syzygy A (coefficient R G M) n
  let e := ActualModuleRestriction.restrictionIso (NoncommGroupAlgebraModule.scalarHom R Q)
    (ModuleCat.of A (T →₀ A)) (ModuleCat.of R (T →₀ A)) (AddEquiv.refl _) (by
      intro r f
      ext t g
      change (MonoidAlgebra.single 1 r * f t).coeff g = r * (f t).coeff g
      exact MonoidAlgebra.coeff_single_one_mul _ _ _)
  letI : Module.Projective R (T →₀ A) := inferInstance
  exact Module.Projective.of_equiv e.toLinearEquiv.symm

/-- Finite R and the genuine finite quotient give finite terms of this actual construction. -/
theorem term_finite [Finite R] (n : ℕ) : Finite ((complex R G M).X n).obj.V := by
  letI : Finite (MonoidAlgebra R (G ⧸ (kernel R G M).toSubgroup)) :=
    NoncommGroupAlgebraModule.ring_finite R (G ⧸ (kernel R G M).toSubgroup)
  letI : Finite (coefficient R G M) := inferInstanceAs (Finite M.obj.V)
  exact FiniteFreeModuleResolution.term_finite
    (MonoidAlgebra R (G ⧸ (kernel R G M).toSubgroup)) (coefficient R G M) n

end FiniteQuotientCoefficientResolution
