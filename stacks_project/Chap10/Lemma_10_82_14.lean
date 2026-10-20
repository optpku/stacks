/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
@stack 0H9I
# Lemma 10.82.14

For an algebra map `R → S` that is universally injective as an `R`-linear
map, right tensoring with `S` reflects injections, surjections, and
isomorphisms.  The three reusable statements are recalled directly from the
`LinearMap` owner below.
-/

@[stacks 0H9I "injectivity reflection"]
#check LinearMap.injective_of_rTensor_of_universallyInjective

@[stacks 0H9I "surjectivity reflection"]
#check LinearMap.surjective_of_rTensor_of_universallyInjective

@[stacks 0H9I "bijectivity reflection"]
#check LinearMap.bijective_of_rTensor_of_universallyInjective
