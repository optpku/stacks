/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Cr
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Tsen
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

universe u

namespace BrauerGroup

/-- Every Brauer class of the function field of a curve over an algebraically closed
field is the neutral class. -/
theorem eq_one_of_curve {k : Type u} [Field k] [IsAlgClosed k]
    (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
    (A : Br(X.left.functionField)) : A = 1 := sorry

end BrauerGroup

end
