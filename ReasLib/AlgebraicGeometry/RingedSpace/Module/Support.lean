/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Supports of module sheaves on ringed spaces

This file specializes the generic support API to the structure sheaf and module category of a
ringed space. The topological additive/ring support and arbitrary module-sheaf support owners are
imported from their neutral modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

section Support

/-- Support of an `𝒪_X`-module: points where the stalk is nonzero. -/
@[stacks 01AT "ringed-space module support"]
abbrev moduleSupport (ℱ : X.Modules) : Set X :=
  SheafOfModules.support ℱ

/-- A module sheaf is supported at a point exactly when its stalk has a nonzero element. -/
@[simp]
theorem mem_moduleSupport_iff (ℱ : X.Modules) (x : X) :
    x ∈ moduleSupport ℱ ↔ ∃ m : stalkModuleCat ℱ x, m ≠ 0 := sorry

/-- The object property of being supported on a subset `T`. -/
abbrev moduleSupportedOn (T : Set X) : ObjectProperty X.Modules :=
  SheafOfModules.supportedOn T

end Support

end AlgebraicGeometry.RingedSpace
