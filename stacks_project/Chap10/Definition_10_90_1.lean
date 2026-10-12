/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Coherent.Basic

@[expose] public section

/-!
# Chapter 10 Compatibility Facade

Definition 10.90.1 is owned by the neutral coherent-module API.

@stack 05CV
-/

/- Definition 10.90.1 (Tag 05CV): the source notions of a coherent module and a coherent
commutative ring are `Module.Coherent` and `IsCoherentRing`. -/
@[stacks 05CV "coherent modules"]
#check @Module.Coherent
@[stacks 05CV "coherent commutative rings"]
#check @IsCoherentRing
