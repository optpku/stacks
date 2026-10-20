/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Ample
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology

/-!
# Cohomological criteria involving ample invertible modules

This file gives criteria for ampleness and affineness in terms of cohomology and tensor powers
of invertible modules.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section

variable [CompactSpace X.carrier]

/-- An invertible module on a quasi-compact scheme is ample if every quasi-coherent ideal
subobject has a positive tensor twist with vanishing first cohomology. -/
theorem isAmple_of_H1_vanishes_for_quasiCoherent_idealSheaf_tensorPowers
    (L : X.Modules) [hL : Invertible L]
    (hH1 : ∀ I : Scheme.IdealSubobject X, I.toModule.IsQuasicoherent →
      ∃ n : ℕ, 0 < n ∧
        IsZero
          (((SheafOfModules.toSheaf X.ringCatSheaf).obj
            (I.toModule ⊗ RingedSpace.TensorPower.sheaf L n)).H' 1 (⊤ : X.Opens))) :
    IsAmple L := sorry

end


/-- A scheme is affine if the positive-degree cohomology of all sufficiently negative tensor
powers of an ample invertible module vanishes. -/
theorem isAffine_of_isAmple_higherCohomology_neg_tensorPower_isZero
    (L : X.Modules) [Invertible L] [IsAmple L] (n₀ : ℤ)
    (hvanish : ∀ n : ℤ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
      IsZero (RingedSpace.moduleCohomology (tensorPowerInt L (-n)) p)) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

variable {X : Scheme.{u}}

/-- A quasi-affine scheme with vanishing positive-degree cohomology of its structure sheaf is
affine. -/
@[stacks 0EBE]
theorem isAffine_of_structureSheaf_higherCohomology_isZero
    (hX : X.IsQuasiAffine)
    (hvanish : ∀ p : ℕ, 0 < p →
      IsZero (RingedSpace.moduleCohomology (SheafOfModules.unit X.ringCatSheaf : X.Modules) p)) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme.IsQuasiAffine
