/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.Etale
import StacksCheckRecall

/-!
# Lemma 15.44.2

@stack 07QP
-/

@[expose] public section

/- Lemma 15.44.2 (07QP): an étale map preserves the Krull dimension of the localizations at a
prime and its contraction. -/
@[stacks 07QP "etale local Krull-dimension invariance"]
#check @Algebra.Etale.ringKrullDim_localizationAtPrime_eq
