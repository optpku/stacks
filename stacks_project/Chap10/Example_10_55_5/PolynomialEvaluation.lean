/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Equalizer.Finite
import StacksCheckRecall

/-!
# Finite normalization of the equal-endpoint algebra

@stack 00JG

The reusable statement is generalized to two distinct evaluation points in
`Polynomial.EvalEqualizer`; this helper records the specialization used in Example 10.55.5.
-/

@[expose] public section

@[stacks 00JG "two-generator normalization"]
#check @Polynomial.EvalEqualizer.generatorMap

@[stacks 00JG "surjective normalization map"]
#check @Polynomial.EvalEqualizer.generatorMap_surjective

@[stacks 00JG "finite normalization"]
#check @Polynomial.EvalEqualizer.moduleFinite

@[stacks 00JG "common-endpoint evaluation"]
#check @Polynomial.EqualEndpoint.eval

@[stacks 00JG "finite polynomial normalization"]
#check @Polynomial.EqualEndpoint.polynomialModuleFinite

@[stacks 00JG "finite endpoint module"]
#check @Polynomial.EqualEndpoint.endpointModuleFinite
