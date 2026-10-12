/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.Criteria

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A closed point of a one-dimensional locally algebraic scheme over a finite separable
field extension is a node if and only if it is a node after restriction to the smaller
field. -/
theorem isNode_iff_restrictScalars
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [Algebra.IsSeparable k k'] (X : SchemeOverField k') [LocallyAlgebraic X]
    (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (h_closed : x ∈ closedPoints X.left) :
    isNode X x ↔ isNode ((Over.map (FieldExtension.specMap k k')).obj X) x := sorry

end AlgebraicGeometry.SchemeOverField
