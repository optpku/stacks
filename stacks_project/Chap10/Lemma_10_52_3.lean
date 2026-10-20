module

public import Mathlib.RingTheory.Length
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Lemma 10.52.3 (Tag 00IV): if `0 → M' → M → M'' → 0` is a short exact sequence of `R`-modules,
then the length of `M` is the sum of the lengths of `M'` and `M''`.

@stack 00IV
-/
@[stacks 00IV]
#check @Module.length_eq_add_of_exact
