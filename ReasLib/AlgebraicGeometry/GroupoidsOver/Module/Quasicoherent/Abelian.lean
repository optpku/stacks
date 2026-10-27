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

/-- Quasi-coherent modules are closed under kernels. -/
instance quasiCoherentModuleProperty.isClosedUnderKernels (X : GroupoidsOver S) [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).IsClosedUnderKernels :=
  sorry

/-- Quasi-coherent modules are closed under cokernels. -/
instance quasiCoherentModuleProperty.isClosedUnderCokernels (X : GroupoidsOver S) [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).IsClosedUnderCokernels :=
  sorry

/-- Quasi-coherent modules are closed under finite products. -/
instance quasiCoherentModuleProperty.isClosedUnderFiniteProducts (X : GroupoidsOver S) [AlgebraicStack X] :
    (quasiCoherentModuleProperty X).IsClosedUnderFiniteProducts :=
  sorry

/-- Quasi-coherent modules on an algebraic stack form an abelian category. -/
instance QCoh.instAbelian (X : GroupoidsOver S) [AlgebraicStack X] :
    Abelian (QCoh X) :=
  inferInstanceAs (Abelian (quasiCoherentModuleProperty X).FullSubcategory)


end AlgebraicGeometry.GroupoidsOver
