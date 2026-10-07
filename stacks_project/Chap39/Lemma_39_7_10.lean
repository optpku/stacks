module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Connected

universe u

/- Lemma 39.7.10: A connected group scheme over a field is irreducible. -/
@[stacks 0B7Q] #check
  (AlgebraicGeometry.GroupScheme.instIrreducibleSpaceOfConnected :
    ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj G] [ConnectedSpace G.left], IrreducibleSpace G.left)
