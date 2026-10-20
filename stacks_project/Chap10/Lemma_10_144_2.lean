/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Standard.Counterexample
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.144.2

@stack 00UC

Standard étale algebras are étale and are stable under base change and principal localization,
but they are not stable under composition.
-/

/- Lemma 10.144.2 (1): a standard étale algebra is étale. -/
@[stacks 00UC "(1), standard étale implies étale"]
#check @Algebra.instEtaleOfIsStandardEtale

/- Lemma 10.144.2 (2): a base change of a standard étale algebra is standard étale. -/
@[stacks 00UC "(2), base change"]
#check @Algebra.instIsStandardEtaleTensorProduct

/- Lemma 10.144.2 (3): a principal localization of a standard étale algebra is standard étale. -/
@[stacks 00UC "(3), principal localization"]
#check @Algebra.IsStandardEtale.of_isLocalizationAway

@[stacks 00UC "(4), composition counterexample"]
#check @Algebra.IsStandardEtale.exists_tower_with_nonstandard_composite
