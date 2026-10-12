/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Coherent.Noetherian
import StacksCheckRecall

/-!
# Noetherian rings are coherent

@stack 05CY
-/

@[expose] public section

/-!
# Chapter 10 Compatibility Facade

Lemma 10.90.5 is the standard Noetherian-to-coherent instance in `ReasLib`.
-/

/- Lemma 10.90.5 (Tag 05CY): every Noetherian commutative ring has the instance
`noetherianRing_isCoherentRing`. -/
@[stacks 05CY]
#check @noetherianRing_isCoherentRing
