/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-! # Abelian category of quasi-coherent modules on algebraic stacks -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The zero sheaf of modules is quasi-coherent. -/
instance quasiCoherentModuleProperty.containsZero (X : GroupoidsOver S) [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).ContainsZero :=
  sorry

/-- Quasi-coherent modules are closed under cokernels. -/
instance quasiCoherentModuleProperty.isClosedUnderCokernels (X : GroupoidsOver S) [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).IsClosedUnderCokernels :=
  sorry

/-- Quasi-coherent modules are closed under finite products. -/
instance quasiCoherentModuleProperty.isClosedUnderFiniteProducts (X : GroupoidsOver S) [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).IsClosedUnderFiniteProducts :=
  sorry

/-- Intrinsic kernels and normality in the category of quasi-coherent modules.
These follow by descent to a smooth presentation (Stacks, Tag 06WV (1)--(2)).
The kernels here are taken in `QCoh X`: the ambient big-fppf kernel need not
be quasi-coherent, since objects of that site need not be flat over `X`. -/
theorem QCoh.abelian_criteria (X : GroupoidsOver S) [AlgebraicStack X] :
    Limits.HasKernels (QCoh X) ∧
      IsNormalMonoCategory (QCoh X) ∧ IsNormalEpiCategory (QCoh X) :=
  sorry

/-- Quasi-coherent modules on an algebraic stack form an abelian category.
This uses intrinsic kernels, not closure under ambient big-fppf kernels;
the inclusion into all module sheaves is in general only right exact. -/
instance QCoh.instAbelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (QCoh X) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := (QCoh.abelian_criteria X).2.1
  toIsNormalEpiCategory := (QCoh.abelian_criteria X).2.2
  has_finite_products := inferInstance
  has_kernels := (QCoh.abelian_criteria X).1
  has_cokernels := inferInstance


end AlgebraicGeometry.GroupoidsOver
