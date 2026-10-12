/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.AtPrime.Locality

@[expose] public section

/-!
# Primewise Smoothness Recall

The shared theorem owns the local-to-global comparison; this source item is a
tagged recall of that canonical API.

@stack 00TC
-/

/- Lemma 10.137.12, tag 00TC: `R → S` is smooth if and only if every prime of
`S` has a principal-open neighbourhood on which the localized `R`-algebra is
smooth. -/
@[stacks 00TC "smoothness is local at target primes"]
#check @Algebra.Smooth.iff_forall_smoothAtPrime
