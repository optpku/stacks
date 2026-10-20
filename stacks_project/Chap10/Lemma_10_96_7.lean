/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.IdealGenerators
import StacksCheckRecall

@[expose] public section

/-!
@stack 090S
# Lemma 10.96.7

The reusable finite-generator statements are owned by
`ReasLib.RingTheory.AdicCompletion.IdealGenerators`.
-/

/- Lemma 10.96.7 (1): precompleteness for each principal generator implies
precompleteness for the finitely generated ideal. -/
@[stacks 090S "(1)"]
#check @IsPrecomplete.of_span_eq_of_generatorwise

/- Lemma 10.96.7 (2): generatorwise surjectivity of the completion maps implies
surjectivity for the finitely generated ideal. -/
@[stacks 090S "(2)"]
#check @AdicCompletion.surjective_of_span_eq_of_generatorwise
