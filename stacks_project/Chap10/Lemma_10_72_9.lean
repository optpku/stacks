/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.AssociatedPrime
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.72.9
@stack 0BK4

For a finite module over a Noetherian local ring, the quotient by any associated prime has
Krull dimension at least the module depth.  The statement is owned canonically in `Module`.
-/

@[stacks 0BK4]
#check @Module.depth_le_krullDim_quotient

end
