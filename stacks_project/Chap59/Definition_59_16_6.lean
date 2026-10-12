/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DescentDatum.Effectivity
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 59.16.6: a module descent datum is effective when it is
isomorphic to the canonical datum obtained from scalar extension of some
module over the base ring. -/
@[stacks 03OC] #check (@Module.DescentDatum.IsEffective :
  (A B N : Type u) → [CommRing A] → [CommRing B] → [Algebra A B] →
    [AddCommGroup N] → [Module A N] → [Module B N] →
    [IsScalarTower A B N] → [SMulCommClass A B N] →
    Module.DescentDatum A B N → Prop)
