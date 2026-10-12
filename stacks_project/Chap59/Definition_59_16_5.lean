/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DescentDatum
import StacksCheckRecall

@[expose] public section

universe u v w

/- Definition 59.16.5: a descent datum for a `B`-module `N` along a ring map
`A → B` is the bundled module descent datum with its tensor cocycle condition. -/
@[stacks 03OB] #check (@Module.DescentDatum :
  (A : Type u) → (B : Type v) → (N : Type w) →
    [CommRing A] → [CommRing B] → [Algebra A B] →
      [AddCommGroup N] → [Module A N] → [Module B N] →
        [IsScalarTower A B N] → [SMulCommClass A B N] →
          Type (max v w))
