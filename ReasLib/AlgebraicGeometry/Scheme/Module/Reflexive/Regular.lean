/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Reflexive modules on low-dimensional regular schemes

This file characterizes coherent reflexive modules on regular schemes of topological Krull
dimension at most two.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on a regular scheme of topological Krull dimension at most two is reflexive
if and only if it is finite locally free. -/
@[stacks 0B3N]
theorem isReflexive_iff_isFiniteLocallyFree_of_topologicalKrullDim_le_two
    {X : Scheme.{u}} [Scheme.Regular X] (ℱ : X.Modules) [ℱ.IsCoherent]
    (hdim : topologicalKrullDim X ≤ 2) :
    IsReflexive ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
