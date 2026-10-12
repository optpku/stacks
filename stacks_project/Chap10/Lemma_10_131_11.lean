/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.Quotient.Pow
import StacksCheckRecall

/-!
# Lemma 10.131.11
@stack 02HQ
-/

@[expose] public section

/- Lemma 10.131.11 [stacks 02HQ]: the quotient by `I ^ (n + 1)` induces a
bijective Kähler base-change map after base change to `S ⧸ I ^ n`.  The
source's assumption `1 ≤ n` is unnecessary in the canonical formulation,
which also covers `n = 0`. -/
@[stacks 02HQ "successive ideal-power Kähler base change"]
#check @KaehlerDifferential.Quotient.Pow.baseChange_bijective

@[stacks 02HQ "successive ideal-power base-change map"]
#check @KaehlerDifferential.Quotient.Pow.baseChange
@[stacks 02HQ "successive ideal-power bijection companion"]
#check @KaehlerDifferential.Quotient.Pow.baseChange_bijective
