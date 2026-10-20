/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Semicontinuity.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberIntegral.BaseChange
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood

/-!
# Semicontinuity of weightings
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A strictly positive integer-valued weighting of a locally quasi-finite morphism is upper
semicontinuous on the source. -/
theorem IsWeighting.upperSemicontinuous {X Y : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {w : X → ℤ}
    (hw : f.IsWeighting w) (h_pos : ∀ x, 0 < w x) : UpperSemicontinuous w := sorry

/-- The fibre integral of a strictly positive integer-valued weighting of a separated,
locally quasi-finite morphism with finite fibres is lower semicontinuous on the target. -/
theorem IsWeighting.lowerSemicontinuous_fiberIntegral
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [hf : Filter.TendstoCofinite (fun x : X ↦ f x)] {w : X → ℤ}
    (hw : f.IsWeighting w) (h_pos : ∀ x, 0 < w x) :
    LowerSemicontinuous (f.fiberIntegral hf w) := sorry

end AlgebraicGeometry.Scheme.Hom
