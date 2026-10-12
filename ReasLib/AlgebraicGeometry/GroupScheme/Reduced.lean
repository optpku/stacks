/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

universe u

namespace AlgebraicGeometry.GroupScheme

/-- A group scheme over a characteristic-zero field has reduced underlying scheme. -/
instance instIsReducedOfCharZero {k : Type u} [Field k] [CharZero k]
    (G : AlgebraicGeometry.SchemeOverField k) [CategoryTheory.GrpObj G] :
    AlgebraicGeometry.IsReduced G.left := sorry

end AlgebraicGeometry.GroupScheme
