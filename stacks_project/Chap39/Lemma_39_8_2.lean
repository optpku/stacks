/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Smooth

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Lemma 39.8.2: a locally algebraic group scheme over a characteristic-zero field has smooth
structure morphism. -/
@[stacks 047N] #check
  (AlgebraicGeometry.GroupScheme.instSmoothOfCharZero :
    ∀ {k : Type u} [Field k] [CharZero k] (G : SchemeOverField k) [GrpObj G]
      [LocallyAlgebraic G], Smooth G.hom)
