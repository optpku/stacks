module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.36.15

@stack 02JM
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.15 (1): let `A → B → C` be ring maps. If `A → C` is integral, then so is `B → C`.
This is exactly the canonical mathlib theorem `RingHom.IsIntegral.tower_top`. -/
@[stacks 02JM "(1)"]
#check @RingHom.IsIntegral.tower_top

/- Lemma 10.36.15 (2): let `A → B → C` be ring maps. If `A → C` is finite, then so is `B → C`.
This is exactly the canonical mathlib theorem `RingHom.Finite.of_comp_finite`. -/
@[stacks 02JM "(2)"]
#check @RingHom.Finite.of_comp_finite
