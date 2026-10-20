/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
import StacksCheckRecall

/-!
# Lemma 10.82.13

@stack 0AS5
-/

@[expose] public section

/- Lemma 10.82.13: for a map into a flat module, universal injectivity is detected after
reduction modulo every finitely generated ideal. -/
@[stacks 0AS5 "universal injectivity gives quotient injectivity"]
#check LinearMap.injective_quotientMapByIdeal_of_universallyInjective
@[stacks 0AS5]
#check @LinearMap.universallyInjective_iff_injective_mod_finite_ideal
@[stacks 0AS5 "maximal-ideal criterion"]
#check LinearMap.universallyInjective_of_injective_mod_maximalIdeal
