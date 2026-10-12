/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Connected

universe u

/- Lemma 39.7.10: A connected group scheme over a field is irreducible. -/
@[stacks 0B7Q] #check
  (AlgebraicGeometry.GroupScheme.instIrreducibleSpaceOfConnected :
    ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj G] [ConnectedSpace G.left], IrreducibleSpace G.left)
