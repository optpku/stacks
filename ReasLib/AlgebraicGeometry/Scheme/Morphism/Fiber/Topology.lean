/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The inclusion of a scheme-theoretic fibre is a topological embedding whose image is the
set-theoretic fibre. -/
theorem fiberTopology {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    Topology.IsEmbedding (f.fiberι y) ∧ Set.range (f.fiberι y) = f ⁻¹' {y} := sorry

end AlgebraicGeometry.Scheme.Hom
