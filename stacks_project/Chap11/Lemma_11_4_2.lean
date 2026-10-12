/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.SimpleRing.Center
import StacksCheckRecall

@[expose] public section

/-! Lemma 11.4.2 is the finite-field-extension property of the center of a simple algebra. -/

@[stacks 074A] #check @Subalgebra.center_finiteFieldExtension

end
