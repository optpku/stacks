/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Projective.LocalRing
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.85.3

@stack 0592

Every element of a projective module over a local ring lies in a free direct
summand. The canonical owner proves the stronger statement that the whole
projective module is free, so the source conclusion follows by taking the
whole module as the direct summand.
-/

/- Lemma 10.85.3: every element of a projective module over a local ring is contained in a free
direct summand. -/
@[stacks 0592 "stronger whole-module freeness owner"]
#check @Module.Projective.free_of_isLocalRing

@[stacks 0592 "complemented submodule owner"]
#check @Complementeds
