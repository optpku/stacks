/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Existence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.127.14

@stack 00QY
-/

/- Lemma 10.127.14 [stacks 00QY]: every commutative-ring homomorphism admits
a directed approximation by finite-type stage homomorphisms.  The canonical
owner is `Ring.DirectLimit.Algebra.Approximation.FiniteType`; the source
statement is its nonemptiness theorem, so Chapter 10 should recall that API
rather than maintain a second stage-system structure. -/
@[stacks 00QY "directed finite-type approximation"]
#check @Ring.DirectLimit.Algebra.Approximation.FiniteType.nonempty
