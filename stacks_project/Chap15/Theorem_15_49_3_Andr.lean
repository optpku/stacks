/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Andre
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 15.49.3 (André)

@stack 0H7U
-/

/- Theorem 15.49.3 (André) (`0H7U`): regularity, the geometrically regular closed-fiber
criterion, and the two adic formal-smoothness criteria are equivalent when the source completion
map is regular. -/
@[stacks 0H7U "Andre criterion for regular local maps"]
#check @regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion
