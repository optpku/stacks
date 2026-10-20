/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Curves over a field

This leaf owns the standard typeclass for a dimension-one variety over a
field, together with its direct dimension and specification API.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k]

/-- A curve over the field `k` is a variety over `k` whose scheme has topological Krull
dimension `1`. -/
@[stacks 0A23]
class Curve (X : Over (Spec (CommRingCat.of k))) : Prop extends Variety X where
  /-- The underlying scheme has topological Krull dimension one. -/
  topologicalKrullDim_eq_one : topologicalKrullDim X.left = 1

/-- A curve over `k` is a variety over `k`. -/
@[stacks 0A23, instance]
instance instVarietyOfCurve (X : Over (Spec (CommRingCat.of k))) [h : Curve X] :
    Variety X :=
  h.toVariety

/-- A variety of topological Krull dimension one is a curve over its field. -/
instance instCurveOfFact (V : Over (Spec (CommRingCat.of k))) [Variety V]
    [Fact (topologicalKrullDim V.left = 1)] : Curve V where
  toVariety := inferInstance
  topologicalKrullDim_eq_one := Fact.out

/-- The underlying scheme of a curve has topological Krull dimension `1`. -/
@[stacks 0A23]
theorem topologicalKrullDim_eq_one (X : Over (Spec (CommRingCat.of k))) [h : Curve X] :
    topologicalKrullDim X.left = 1 := sorry

/-- A curve over `k` consists of the corresponding variety structure together with the
dimension-one condition. -/
@[stacks 0A23]
theorem Curve.spec (X : Over (Spec (CommRingCat.of k))) [h : Curve X] :
    Variety X ∧ topologicalKrullDim X.left = 1 := sorry

/-- Unfold `Curve X` into the corresponding variety condition together with the dimension-one
clause. -/
@[stacks 0A23]
theorem curve_iff (X : Over (Spec (CommRingCat.of k))) :
    Curve X ↔ Variety X ∧ topologicalKrullDim X.left = 1 := sorry

end

end AlgebraicGeometry
