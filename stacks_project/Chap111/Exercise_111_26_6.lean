/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Node.EulerPoincare
import StacksCheckRecall

/-!
Euler-Poincaré functions on finite modules over the node coordinate ring
`k[x, y] / (xy)`.
-/

@[expose] public section

universe u

/- Exercise 111.26.6: Euler-Poincaré functions on finite modules over
`k[x, y] / (xy)` for an algebraically closed field `k` are classified by their values
on the quotient by `(y)` and the quotient by `(x)`, in that order. -/
@[stacks 02E4] #check (NodeCoordinateRing.evalAxisPair_bijective :
  ∀ {k : Type u} [Field k] [IsAlgClosed k],
    Function.Bijective (NodeCoordinateRing.evalAxisPair k))
