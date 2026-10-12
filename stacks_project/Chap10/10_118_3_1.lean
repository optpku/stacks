/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GenericFlatness.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Generic-Flatness Localization Condition

The displayed condition in Lemma 10.118.3 is recalled through its canonical
ReasLib proposition.

@stack 051U
-/

/- Equation 10.118.3.1: after localizing at `f`, the algebra is finitely
presented over the localized base, the module is finitely presented over the
localized algebra, and both are free over the localized base. -/
@[stacks 051U]
#check @GenericFlatness.LocalizationCondition
