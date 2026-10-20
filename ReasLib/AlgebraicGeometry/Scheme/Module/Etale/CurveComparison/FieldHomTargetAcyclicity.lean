/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldTraceStalkResolution
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomTargetComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldHomCochainComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace FieldHomTargetAcyclicity
variable (k : Type u) [Field k] (n : ℕ) [NeZero n]
variable {R : Type (u + 1)} [Ring R]
variable (h : ActualRootsModule.Coeff.{u} n →+* R)
variable (hc : ∀ (a : ActualRootsModule.Coeff.{u} n) (r : R), h a * r = r * h a)
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))]
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable [(Spec (CommRingCat.of k)).smallEtaleTopology.HasSheafCompose
  (ModuleCat.restrictScalars (NoncommLocalHom.opScalarHom h hc))]

section Column
variable (F : Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} R))
variable [Finite ((FieldFiniteHomStalk.stalk k R).obj F)]

/-- The actual field-target augmentation is Hom-acyclic for this finite source.
The proof uses regular-A injectivity at the stalk and a specified contraction;
it does not use exactness of Hom_A(F,-) on arbitrary short exact sequences. -/
theorem column_quasiIso :
    QuasiIso (((FieldFiniteHomStalk.localHom k h hc F).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (ResidualNormalizedRootsTrace.fieldTargetNatMap (k := k) n)) := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (FieldFiniteHomStalk.stalkAb k Rᵐᵒᵖ)).1
  apply (FieldFiniteHomStalk.quasiIso_iff k h hc F _).2
  exact FieldTraceStalkResolution.mapped_fieldTargetNatMap_quasiIso k n
    (FieldFiniteHomStalk.moduleHom k h F)
end Column

variable (L : ChainComplex (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable {J K : CochainComplex (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))) ℕ}
variable (g : J ⟶ K)

/-- Finite-diagonal first-quadrant totalization preserves a map which is a
quasi-isomorphism in every specified target column. The hypothesis is on the
actual Hom columns, not merely on g; no source-flatness claim is hidden here. -/
theorem total_quasiIso
    (columns : ∀ i : ℕ, QuasiIso
      (((FieldFiniteHomStalk.localHom k h hc (L.X i)).mapHomologicalComplex (ComplexShape.up ℕ)).map g)) :
    QuasiIso (LocalHomTargetComparison.map h hc (Spec (CommRingCat.of k)) L g) := by sorry

theorem shifted_quasiIso
    (columns : ∀ i : ℕ, QuasiIso
      (((FieldFiniteHomStalk.localHom k h hc (L.X i)).mapHomologicalComplex (ComplexShape.up ℕ)).map g)) :
    QuasiIso (LocalHomTargetComparison.shiftedMap h hc (Spec (CommRingCat.of k)) L g) := by
  -- Local instance justification (proof-local temporary data): totalization uses the proved actual Hom-column quasi-isomorphisms.
  letI := total_quasiIso k n h hc L g columns
  -- Local instance justification (proof-local temporary data): integer extension preserves this particular total map.
  letI : QuasiIso (LocalHomTargetComparison.integerMap h hc (Spec (CommRingCat.of k)) L g) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance
  unfold LocalHomTargetComparison.shiftedMap
  exact (CochainComplex.quasiIso_shift_iff _ _).2 inferInstance

variable (B : ChainComplex (DiscreteModuleCat R Gal(AlgebraicClosure k/k)) ℕ)

/-- The exact augmentation used by characterMap, with all source terms finite.
This is the particular self-injective trace coefficient case, for arbitrary R. -/
theorem traceAugmentation_quasiIso (hB : ∀ i : ℕ, Finite (B.X i).obj.V) :
    QuasiIso (LocalHomTargetComparison.shiftedMap h hc (Spec (CommRingCat.of k))
      (FieldHomCochainComparison.fieldB B)
      (ResidualNormalizedRootsTrace.fieldTargetNatMap (k := k) n)) := by
  apply shifted_quasiIso k n h hc
  intro i
  -- Local instance justification (proof-local temporary data): the specified source chain term is finite.
  letI : Finite (B.X i).obj.V := hB i
  -- Local instance justification (proof-local temporary data): the actual field counit transports that finiteness to its associated-sheaf stalk.
  letI := FieldFiniteHomStalk.inverse_stalk_finite k R (B.X i)
  exact column_quasiIso k n h hc ((FieldModuleDescent.inverse k R).obj (B.X i))

end FieldHomTargetAcyclicity
