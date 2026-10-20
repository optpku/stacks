/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.UniversalHomeomorphism

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Reduction preserves the topological Krull dimension of a scheme. -/
theorem topologicalKrullDim_reduction (X : Scheme.{u}) :
    topologicalKrullDim X.reduction = topologicalKrullDim X := sorry

end AlgebraicGeometry.Scheme
