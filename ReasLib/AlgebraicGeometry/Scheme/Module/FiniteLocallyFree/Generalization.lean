/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Inseparable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Every finite flat quasi-coherent module on a scheme is finite locally free if and only if
every closed subset stable under generalization is open. -/
@[stacks 053N]
theorem finiteFlat_finiteLocallyFree_iff_closed_stableUnderGeneralization_isOpen
    (X : Scheme.{u}) :
    (∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] [ℱ.IsFlat],
      ℱ.IsFiniteLocallyFree) ↔
      ∀ Z : Set X, IsClosed Z → StableUnderGeneralization Z → IsOpen Z := sorry

end AlgebraicGeometry.Scheme.Modules
