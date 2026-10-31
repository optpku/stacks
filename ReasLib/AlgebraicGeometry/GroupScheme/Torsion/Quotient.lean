/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Released under Apache 2.0 license as described in the file LICENSE.
This module specializes Mathlib's actual group-theoretic torsion and quotient
constructions to the canonical functor-of-points group of a scheme.
-/
module

public import ReasLib.AlgebraicGeometry.GroupScheme.Torsion.Group
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# The torsion subgroup and arithmetic point quotients

The quotient by all finite-order points, used for heights and rank, and the
quotient by multiples, used in weak Mordell--Weil descent, are distinct actual
Mathlib quotient groups. Neither is a hypothesis packaged as a construction.
No field, finite generation, or geometric property of the group is required.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.GroupObject

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G] (T : Over S)

/-- Mathlib's integer-annihilator subgroup is the same actual `n`-torsion point set. -/
def additiveTorsionEquiv (n : ℕ) :
    AddSubgroup.torsionBy (AdditivePoints G T) (n : ℤ) ≃ TorsionPoints G T n where
  toFun x := ⟨x.1.toMul, by
    have hx : n • x.1 = 0 := AddSubgroup.torsionBy.nsmul_iff.mp x.2
    exact congrArg Additive.toMul hx⟩
  invFun x := ⟨Additive.ofMul x.1, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    exact congrArg Additive.ofMul x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The actual additive `n`-torsion subgroup is represented by the multiplication kernel. -/
def torsionByEquivSchemeKerPoints (n : ℕ) :
    AddSubgroup.torsionBy (AdditivePoints G T) (n : ℤ) ≃
      (T ⟶ multiplicationKernel G n) :=
  (additiveTorsionEquiv G T n).trans (torsionSubsetEquivSchemeKerPoints G T n)

@[simp]
theorem torsionByEquivSchemeKerPoints_comp_inclusion (n : ℕ)
    (x : AddSubgroup.torsionBy (AdditivePoints G T) (n : ℤ)) :
    torsionByEquivSchemeKerPoints G T n x ≫ kernelInclusion G n = x.1.toMul :=
  torsionSubsetEquivSchemeKerPoints_comp_inclusion G T n (additiveTorsionEquiv G T n x)

/-- All finite-order points in the actual additive point group. -/
abbrev pointTorsion : AddSubgroup (AdditivePoints G T) :=
  AddCommGroup.torsion (AdditivePoints G T)

/-- The actual quotient by all finite-order points, for height and rank arguments. -/
abbrev PointsModuloTorsion := AdditivePoints G T ⧸ pointTorsion G T

/-- The actual quotient by the subgroup of `n`-multiples, for weak Mordell--Weil. -/
abbrev PointsModuloMultiples (n : ℕ) :=
  AdditivePoints G T ⧸ (nsmulAddMonoidHom (α := AdditivePoints G T) n).range

/-- Membership in the torsion subgroup means some positive multiple is zero. -/
theorem mem_pointTorsion_iff (x : AdditivePoints G T) :
    x ∈ pointTorsion G T ↔ ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  change IsOfFinAddOrder x ↔ ∃ n : ℕ, 0 < n ∧ n • x = 0
  exact isOfFinAddOrder_iff_nsmul_eq_zero

/-- The zero class modulo torsion is exactly the class of a finite-order point. -/
theorem mk_moduloTorsion_eq_zero_iff (x : AdditivePoints G T) :
    (QuotientAddGroup.mk x : PointsModuloTorsion G T) = 0 ↔
      ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, mem_pointTorsion_iff]

/-- The zero class modulo `n` is exactly an actual `n`-multiple. -/
theorem mk_moduloMultiples_eq_zero_iff (n : ℕ) (x : AdditivePoints G T) :
    (QuotientAddGroup.mk x : PointsModuloMultiples G T n) = 0 ↔
      ∃ y : AdditivePoints G T, n • y = x := by
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

end AlgebraicGeometry.Scheme.GroupObject
