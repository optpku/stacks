/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay

/-!
# Cohen–Macaulayness of reduced schemes

Reduced locally Noetherian schemes of topological Krull dimension at most one
are Cohen–Macaulay.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.CohenMacaulay

/-- A reduced locally Noetherian scheme of topological Krull dimension at most `1` is
Cohen–Macaulay. -/
theorem of_isReduced_of_topologicalKrullDim_le_one
    (X : Scheme.{u}) [IsReduced X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) :
    Scheme.CohenMacaulay X := sorry

end AlgebraicGeometry.Scheme.CohenMacaulay
