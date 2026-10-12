/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Unramified.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.148.2

@stack 0H91
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.148.2: if `R → S` is formally unramified, then for any ring map `R → R'`, the base
change `R' ⊗[R] S` is formally unramified over `R'`. This is the canonical mathlib base-change
instance `Algebra.FormallyUnramified.base_change`. -/
@[stacks 0H91]
#check @Algebra.FormallyUnramified.base_change
