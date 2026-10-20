/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.Operations
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.82.10 (Tag 05CJ): universal injectivity is left-cancellative under composition.

@stack 05CJ
-/
@[stacks 05CJ]
#check LinearMap.universallyInjective_of_comp
