module

public import Mathlib.RingTheory.Smooth.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Lemma 10.137.3 (Tag 00T4): if `R → S` is smooth, then for any ring map `R → R'`, the base change
`R' → R' ⊗[R] S` is again smooth.
@stack 00T4
-/
@[stacks 00T4]
#check @Algebra.Smooth.baseChange
