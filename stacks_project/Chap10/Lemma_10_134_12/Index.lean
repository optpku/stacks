/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.LocalizationAway
import StacksCheckRecall

@[expose] public section

/-!
# Shared index for Lemma 10.134.12

The chapter support path reexports the shared localization-away API.  New
consumers should import `ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.LocalizationAway`.

@stack 08JZ
-/

@[stacks 08JZ "canonical localization comparison"]
#check @Algebra.NaiveCotangent.LocalizationAway.comparison

@[stacks 08JZ "canonical localization comparison is an isomorphism"]
#check @Algebra.NaiveCotangent.LocalizationAway.comparison_isIso
