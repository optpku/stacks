/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.GeneralLinear.UpperTriangular.Action

/-!
# Smoothness of the upper-triangular action groupoid

The source and target morphisms of the inverse-right action groupoid are smooth of relative
dimension three over a field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GLTwo.UpperTriangular

/-- The source map of the action groupoid is smooth of relative dimension three. -/
@[instance]
theorem relationSource_smoothOfRelativeDimension (k : Type u) [Field k] :
    SmoothOfRelativeDimension 3 (relation k).s.left := sorry

/-- The target map of the action groupoid is smooth of relative dimension three. -/
@[instance]
theorem relationTarget_smoothOfRelativeDimension (k : Type u) [Field k] :
    SmoothOfRelativeDimension 3 (relation k).t.left := sorry

end AlgebraicGeometry.GLTwo.UpperTriangular
