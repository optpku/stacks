/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Unibranch

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A point of a one-dimensional locally algebraic scheme over a field is closed and
nodal if and only if a point above it after an arbitrary field extension is closed and
nodal. -/
theorem closedPointAndNode_iff_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [LocallyAlgebraic X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (y : (FieldExtension.Over.baseChange k K X).left)
    (hy : FieldExtension.Over.toSource k K X y = x) :
    (x ∈ closedPoints X.left ∧ isNode X x) ↔
      (y ∈ closedPoints (FieldExtension.Over.baseChange k K X).left ∧
        isNode (FieldExtension.Over.baseChange k K X) y) := sorry

end AlgebraicGeometry.SchemeOverField
