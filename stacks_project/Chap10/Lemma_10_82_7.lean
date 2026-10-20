/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
import StacksCheckRecall

/-!
# Lemma 10.82.7

@stack 058P
-/

@[expose] public section

/- Lemma 10.82.7: tensor injectivity and the two flatness consequences of universal exactness are
available from the neutral short-complex API. -/
@[stacks 058P "tensor injectivity"]
#check CategoryTheory.ShortComplex.rTensor_f_injective_of_universallyExact
@[stacks 058P]
#check CategoryTheory.ShortComplex.flat_X₁_and_X₃_of_universallyExact
@[stacks 058P "source flatness"]
#check CategoryTheory.ShortComplex.UniversallyExact.flat_X₁
@[stacks 058P "cokernel flatness"]
#check CategoryTheory.ShortComplex.UniversallyExact.flat_X₃
