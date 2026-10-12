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
# Localization-away support for Lemma 10.134.12

The former coordinate calculations for a particular localized self-presentation
are proof infrastructure.  The public presentation-level and canonical owners
now live in the neutral ReasLib localization-away leaf.

@stack 08JZ
-/

open scoped TensorProduct

@[stacks 08JZ "presentation-level localization comparison"]
#check @Algebra.Extension.NaiveCotangent.LocalizationAway.modelComparison
@[stacks 08JZ "presentation-level localization comparison is an isomorphism"]
#check @Algebra.Extension.NaiveCotangent.LocalizationAway.modelComparison_isIso
@[stacks 08JZ "literal scalar-extension localization comparison"]
#check @Algebra.Extension.NaiveCotangent.LocalizationAway.comparison
@[stacks 08JZ "literal localization comparison is an isomorphism"]
#check @Algebra.Extension.NaiveCotangent.LocalizationAway.comparison_isIso
@[stacks 08JZ "canonical localization comparison"]
#check @Algebra.NaiveCotangent.LocalizationAway.comparison
