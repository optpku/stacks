/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.AtPoint
import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Dimension

/-!
# Fibre dimension of syntomic morphisms

The local dimension of the fibres of a syntomic morphism is locally constant
on its source.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Syntomic

/-- The local fibre dimension of a syntomic morphism is locally constant on its source. -/
theorem isLocallyConstant_fiberDimensionAt {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Syntomic f) : IsLocallyConstant (fun x : X ↦ f.fiberDimensionAt x) := sorry

end AlgebraicGeometry.Syntomic
