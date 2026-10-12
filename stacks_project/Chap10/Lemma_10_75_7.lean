/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Finiteness of `Tor`
@stack 0AZ4

The Noetherian finiteness theorem is shared `ModuleCat.Tor` API.  This file retains only the
textbook entry point and its Stacks tag.
-/

-- Lemma 10.75.7, tag `0AZ4`: every `Tor` degree of finite modules over a Noetherian ring is finite.
@[stacks 0AZ4]
#check @CategoryTheory.ModuleCat.Tor.finite
