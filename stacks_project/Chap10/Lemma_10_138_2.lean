/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.138.2

@stack 00TJ
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.138.2: if `R → S` is formally smooth and `R → R'` is any ring map, then the base
change `R' ⊗[R] S` is formally smooth over `R'`. This is the canonical tensor-product base-change
instance `Algebra.FormallySmooth.instTensorProduct`. -/
@[stacks 00TJ]
#check @Algebra.FormallySmooth.instTensorProduct
