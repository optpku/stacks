/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
import StacksCheckRecall

/-!
# Lemma 10.62.1

@stack 00L0
-/

@[expose] public section

/- Lemma 10.62.1: a finite module over a Noetherian ring admits a finite filtration whose
successive quotients are prime quotients of the base ring.  Mathlib owns the existence theorem;
`Module.PrimeFiltration` is the reusable named view of its output. -/
@[stacks 00L0]
#check @IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime

@[stacks 00L0 "prime filtration data"]
#check @Module.PrimeFiltration
