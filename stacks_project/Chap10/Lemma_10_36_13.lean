module

public import Mathlib.RingTheory.RingHom.Integral
public import Mathlib.RingTheory.RingHom.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.36.13

@stack 02JK
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.13 (1): integrality of a ring map is stable under base change. In the chapter's
canonical owner language from Definition `10.36.1`, this is exactly the mathlib declaration
`RingHom.isIntegral_isStableUnderBaseChange`. -/
@[stacks 02JK "(1)"]
#check @RingHom.isIntegral_isStableUnderBaseChange

/- Lemma 10.36.13 (2): finiteness of a ring map is stable under base change. In the chapter's
canonical owner language from Definition `10.7.1`, this is exactly the mathlib declaration
`RingHom.finite_isStableUnderBaseChange`. -/
@[stacks 02JK "(2)"]
#check @RingHom.finite_isStableUnderBaseChange
