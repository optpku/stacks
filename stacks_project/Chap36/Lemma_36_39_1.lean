/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 36.39.1: every scheme admits a coherent determinant functor on perfect derived
objects of Tor-amplitude in `[-1, 0]`, with canonical rank-zero sections and the affine-local
comparison with the ring-level determinant construction. -/
@[stacks 0FJX] #check
  (AlgebraicGeometry.Scheme.PerfectDerived.TorNegOneZero.nonemptyDeterminant :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      Nonempty (AlgebraicGeometry.Scheme.PerfectDerived.TorNegOneZero.Determinant X))
