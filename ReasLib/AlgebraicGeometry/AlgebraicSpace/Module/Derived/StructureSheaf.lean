/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.StructureModule
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.StructureSheaf

/-! # The structure sheaf in the derived category of modules -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure sheaf of an algebraic space, placed in degree zero in `D(𝒪_X)`. -/
abbrev structureSheafDerived {S : Scheme.{u}} (X : AlgebraicSpace S) : ModuleDerived X :=
  (DerivedCategory.singleFunctor (Modules X) 0).obj
    (SheafOfModules.unit (structureSheaf X))

/-- The structure sheaf placed in degree zero has quasi-coherent cohomology. -/
theorem structureSheafDerived_mem {S : Scheme.{u}} (X : AlgebraicSpace S) :
    derivedQuasiCoherentModuleProperty X (structureSheafDerived X) := sorry

end AlgebraicGeometry.AlgebraicSpace
