/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselian
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.153.1

@stack 04GF
-/

/- Definition 10.153.1: the Stacks notion of a henselian local ring is the canonical mathlib
class `HenselianLocalRing`. A local ring is strictly henselian if it is henselian and its
residue field is separably algebraically closed.

Owner: `StrictHenselianLocalRing` in `ReasLib.RingTheory.Henselian.StrictHenselian`. -/
@[stacks 04GF "henselian local ring"]
#check HenselianLocalRing
@[stacks 04GF "strictly henselian local ring"]
#check @StrictHenselianLocalRing
