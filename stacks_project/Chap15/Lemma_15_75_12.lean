/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.LocalizationAway
import StacksCheckRecall

/-!
# Lemma 15.75.12

@stack 066Y

The canonical owner keeps the finite family of ring elements and its unit-ideal hypothesis
explicit, and uses the derived `derivedExtensionOfScalars` object for each `Localization.Away`.
-/

@[expose] public section

open CategoryTheory

@[stacks 066Y "Lemma 15.75.12"]
#check @DerivedCategory.IsPerfect.of_localizationAway_unitIdeal
