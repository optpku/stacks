/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- An étale morphism preserves and reflects closed nodal points on a one-dimensional
locally algebraic scheme over a field. -/
theorem closedPointAndNode_iff_of_etale
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyAlgebraic X]
    (h_dimension : topologicalKrullDim X.left = 1) {Y : Scheme.{u}}
    (f : Y ⟶ X.left) [Etale f] (x : X.left) (y : Y) (hy : f y = x) :
    (x ∈ closedPoints X.left ∧ isNode X x) ↔
      (y ∈ closedPoints Y ∧ isNode (Over.mk (f ≫ X.hom)) y) := sorry

end AlgebraicGeometry.SchemeOverField
