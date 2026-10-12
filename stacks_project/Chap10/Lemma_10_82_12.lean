/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.UniversallyInjective.Localization

@[expose] public section

/-!
# Lemma 10.82.12

Universal injectivity under localization is exposed by the reusable ReasLib predicates and
their stability/comparison theorems.

@stack 05CM
-/

@[stacks 05CM "universal injectivity after restriction of scalars"]
#check @LinearMap.UniversallyInjective.Localization.map_restrictScalars

@[stacks 05CM "universal injectivity localization theorem"]
#check @LinearMap.UniversallyInjective.Localization.map_overLocalization

@[stacks 05CM "universal injectivity over the base versus localized ring"]
#check @LinearMap.UniversallyInjective.Localization.overLocalization_iff
