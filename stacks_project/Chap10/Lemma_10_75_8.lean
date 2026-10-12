/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.Tor
import StacksCheckRecall

@[expose] public section

/-!
# Flatness and `Tor` Vanishing

The reusable flatness criterion is owned by `Module.Flat`.
This source file retains only the textbook entry point and its Stacks tag.

@stack 00M5
-/

-- Lemma 10.75.8, tag `00M5`: the five standard equivalent `Tor`-vanishing criteria for flatness.
@[stacks 00M5]
#check @Module.Flat.tor_tfae
