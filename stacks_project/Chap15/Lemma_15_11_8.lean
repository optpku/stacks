/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.IntegralPair
import StacksCheckRecall

/-!
# Integral extensions of henselian pairs

The integral-transfer instance is owned by `ReasLib`; this chapter file records the source label
directly.

@stack 09XK
-/

@[expose] public section

/- Lemma 15.11.8: an integral extension of a henselian pair is henselian for the extended ideal. -/
@[stacks 09XK]
#check @ideal_map_henselianRing_of_isIntegral
