/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Smooth

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

#check
  (AlgebraicGeometry.GroupScheme.instSmoothOfCharZero :
    ∀ {k : Type u} [Field k] [CharZero k] (G : SchemeOverField k) [GrpObj G]
      [LocallyAlgebraic G], Smooth G.hom)
