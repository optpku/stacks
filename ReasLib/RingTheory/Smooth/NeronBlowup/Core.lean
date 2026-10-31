/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Lift
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Regular
public import ReasLib.RingTheory.Smooth.DVRFactorization

/-!
# Affine Neron blowups of DVR factorizations

This file owns one affine Neron blowup chart, its maps to the source and target,
and the resulting one-step DVR factorization. Iteration and base-change APIs
live in separate leaves.

@stack 0BJ3
-/

@[expose] public section

noncomputable section

open Ideal IsLocalRing
open scoped AffineBlowupChart

universe u v w

namespace Algebra.DVR.Factorization

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L] [IsExtensionOfDiscreteValuationRings R L]

/-- The image of a uniformizer of `R` belongs to the closed center. -/
@[stacks 0BJ3 "uniformizer in the closed center"]
theorem algebraMap_uniformizer_mem_closedIdeal
    {S : Algebra.DVR.Factorization R L} {π : R} (hπ : Irreducible π) :
    algebraMap R S.mid π ∈ S.closedIdeal := by
  change S.toTarget (algebraMap R S.mid π) ∈ maximalIdeal L
  rw [S.toTarget.commutes]
  exact map_nonunit (algebraMap R L) π hπ.not_isUnit

/-- The image of a uniformizer, regarded as an element of the closed center. -/
@[stacks 0BJ3 "Neron blowup parameter"]
def neronBlowupParameter
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) : S.closedIdeal :=
  ⟨algebraMap R S.mid π, algebraMap_uniformizer_mem_closedIdeal hπ⟩

/-- The affine Neron blowup chart attached to a DVR factorization and a uniformizer. -/
@[stacks 0BJ3 "affine Neron blowup chart"]
abbrev NeronBlowup
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :=
  affineBlowupChart S.closedIdeal (S.neronBlowupParameter π hπ)

namespace NeronBlowup

/-- The image in the target DVR of the parameter defining the affine Neron blowup is nonzero. -/
@[stacks 0BJ3 "Neron parameter nonzero"]
theorem targetParameter_ne_zero
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    S.toTarget (S.neronBlowupParameter π hπ) ≠ 0 := by
  change S.toTarget (algebraMap R S.mid π) ≠ 0
  rw [S.toTarget.commutes]
  intro h
  exact hπ.ne_zero (IsExtensionOfDiscreteValuationRings.algebraMap_injective
    (h.trans (map_zero (algebraMap R L)).symm))

/-- In the target DVR, the image of the Neron parameter divides the image of every element of
the closed center. -/
@[stacks 0BJ3 "Neron parameter divides the center"]
theorem targetParameter_dvd_center
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) (x : S.closedIdeal) :
    S.toTarget (S.neronBlowupParameter π hπ) ∣ S.toTarget x := by
  change S.toTarget (algebraMap R S.mid π) ∣ S.toTarget x.1
  rw [S.toTarget.commutes]
  have hmax : maximalIdeal L = Ideal.span {algebraMap R L π} := by
    rw [← IsExtensionOfDiscreteValuationRings.WeaklyUnramified.map_maximalIdeal_eq R L,
      hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  apply Ideal.mem_span_singleton.mp
  rw [← hmax]
  exact x.property

/-- The shared DVR chart data used to evaluate the affine Neron blowup. -/
@[stacks 0BJ3 "Neron blowup target DVR chart map"]
def targetChartMap
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    AffineBlowupChart.ChartMap.DVR (B := L) S.closedIdeal
      (S.neronBlowupParameter π hπ) :=
  AffineBlowupChart.ChartMap.DVR.ofDvd (B := L) S.toTarget.toRingHom
    (targetParameter_ne_zero S π hπ)
    (targetParameter_dvd_center S π hπ)

/-- The canonical ring map from the affine Neron blowup to the target DVR. -/
@[stacks 0BJ3 "Neron blowup target map"]
noncomputable def toTargetRingHom
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    S.NeronBlowup π hπ →+* L :=
  (targetChartMap (L := L) S π hπ).lift

/-- The canonical map from the affine Neron blowup to the target commutes with scalars from the
source DVR. -/
theorem toTargetRingHom_commutes
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) (r : R) :
    toTargetRingHom S π hπ
        (@algebraMap R (S.NeronBlowup π hπ) _ _
          (AffineBlowupChart.instAlgebraOfTower S.closedIdeal
            (S.neronBlowupParameter π hπ)) r) =
      algebraMap R L r := by
  change (targetChartMap S π hπ).lift
    (algebraMap S.mid (S.NeronBlowup π hπ) (algebraMap R S.mid r)) = _
  rw [AffineBlowupChart.ChartMap.DVR.lift_algebraMap]
  exact S.toTarget.commutes r

/-- The canonical `R`-algebra map from the affine Neron blowup to the target DVR. -/
@[stacks 0BJ3 "Neron blowup algebra map"]
noncomputable def toTarget
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    S.NeronBlowup π hπ →ₐ[R] L where
  toRingHom := toTargetRingHom S π hπ
  commutes' := toTargetRingHom_commutes S π hπ

/-- The structural map from the intermediate algebra to its affine Neron blowup commutes with
scalars from the source DVR. -/
theorem fromSource_commutes
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) (r : R) :
    @algebraMap S.mid (S.NeronBlowup π hπ) _ _
        (AffineBlowupChart.instAlgebra S.closedIdeal
          (S.neronBlowupParameter π hπ)) (algebraMap R S.mid r) =
      @algebraMap R (S.NeronBlowup π hπ) _ _
        (AffineBlowupChart.instAlgebraOfTower S.closedIdeal
          (S.neronBlowupParameter π hπ)) r := by
  rfl

/-- The canonical transition map from an intermediate algebra to its affine Neron blowup. -/
@[stacks 0BJ3 "Neron blowup transition"]
noncomputable def fromSource
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    S.mid →ₐ[R] S.NeronBlowup π hπ where
  toRingHom := algebraMap S.mid (S.NeronBlowup π hπ)
  commutes' := fromSource_commutes S π hπ

/-- The transition to the affine Neron blowup preserves the map to the target DVR. -/
@[simp]
theorem toTarget_comp_fromSource
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    (toTarget S π hπ).comp (fromSource S π hπ) = S.toTarget := by
  ext x
  exact AffineBlowupChart.ChartMap.DVR.lift_algebraMap (targetChartMap S π hπ) x

/-- An affine Neron blowup remains flat over the source DVR. -/
instance flat
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    Module.Flat R (S.NeronBlowup π hπ) := by
  letI : Module.IsTorsionFree R (S.NeronBlowup π hπ) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x hx ↦ by
      by_cases hr : r = 0
      · exact Or.inl hr
      · right
        have hrA : algebraMap R S.mid r ∈ nonZeroDivisors S.mid := by
          apply mem_nonZeroDivisors_iff_left.mpr
          intro y hy
          apply Module.Flat.isSMulRegular_of_isRegular (M := S.mid)
            (IsRegular.of_ne_zero hr)
          simpa [Algebra.smul_def] using hy
        have hrN := AffineBlowupChart.algebraMap_mem_nonZeroDivisors S.closedIdeal
          (S.neronBlowupParameter π hπ) (algebraMap R S.mid r) hrA
        apply (mem_nonZeroDivisors_iff_left.mp hrN) x
        change algebraMap R (S.NeronBlowup π hπ) r * x = 0
        simpa only [Algebra.smul_def] using hx
  infer_instance

/-- An affine Neron blowup of a finite-type algebra is again of finite type over the source. -/
instance finiteType
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    Algebra.FiniteType R (S.NeronBlowup π hπ) := by
  let I := S.closedIdeal
  let a := S.neronBlowupParameter π hπ
  letI : IsNoetherianRing S.mid := Algebra.FiniteType.isNoetherianRing R S.mid
  letI : Algebra.FiniteType S.mid (ReesAlgebra.Grading.grade I 0) :=
    Algebra.FiniteType.of_surjective (Algebra.ofId S.mid _) fun x ↦ by
      refine ⟨((x.1 : reesAlgebra I) : Polynomial S.mid).coeff 0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change Polynomial.C _ = _
      simpa only [Polynomial.monomial_zero_left] using
        (ReesAlgebra.Grading.grade_eq_monomial_coeff I 0 x).symm
  letI : IsScalarTower S.mid (ReesAlgebra.Grading.grade I 0) (reesAlgebra I) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FiniteType (ReesAlgebra.Grading.grade I 0) (reesAlgebra I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType S.mid _ _
  letI : Algebra.FiniteType (ReesAlgebra.Grading.grade I 0) (S.NeronBlowup π hπ) :=
    HomogeneousLocalization.Away.finiteType (ReesAlgebra.Grading.degreeOne I a) 1
      (ReesAlgebra.Grading.degreeOne_mem I a)
  letI : IsScalarTower S.mid (ReesAlgebra.Grading.grade I 0) (S.NeronBlowup π hπ) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FiniteType S.mid (S.NeronBlowup π hπ) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType S.mid
      (ReesAlgebra.Grading.grade I 0)) inferInstance
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R S.mid) inferInstance

end NeronBlowup

/-- One deterministic affine Neron blowup, bundled again as a factorization through the fixed
target DVR. -/
@[stacks 0BJ3 "bundled Neron blowup stage"]
noncomputable def neronBlowupStage
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    Algebra.DVR.Factorization R L :=
  Algebra.DVR.Factorization.of (NeronBlowup.toTarget S π hπ)

namespace neronBlowupStage

/-- The bundled Neron blowup stage retains the canonical algebra structure over the preceding
intermediate algebra. -/
@[stacks 0BJ3 "bundled Neron blowup stage source algebra"]
noncomputable instance instAlgebra
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    Algebra S.mid (S.neronBlowupStage π hπ).mid :=
  inferInstanceAs (Algebra S.mid (S.NeronBlowup π hπ))

/-- The source, intermediate, and bundled Neron blowup algebras form the canonical scalar
tower. -/
@[stacks 0BJ3 "bundled Neron blowup stage scalar tower"]
noncomputable instance instIsScalarTower
    [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    IsScalarTower R S.mid (S.neronBlowupStage π hπ).mid := by
  apply IsScalarTower.of_algebraMap_eq'
  rfl

end neronBlowupStage

end Algebra.DVR.Factorization
