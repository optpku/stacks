/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Resolution.Localization

@[expose] public section

/- Lemma 16.9.4: a local resolution at a minimal prime descends to a
resolution of the original map when the target prime localization has Krull
dimension zero. -/
@[stacks 07FA]
#check @AlgHom.ResolvableAtPrime.Localization.of_dimension_zero
