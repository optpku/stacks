/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Transcendence.FiniteType
import StacksCheckRecall

@[expose] public section

/- Lemma 9.26.11 (Tag 037J): if `K/k` is a finitely generated field extension, then the relative
algebraic closure of `k` in `K` is finite-dimensional over `k`.

The reusable finite-transcendence API is owned by
`FieldExtension.existsFiniteTranscendenceBasisFiniteDimensionalOverAdjoin`,
`FieldExtension.basisFieldLinearDisjointOfFiniteAlgebraic`, and
`FieldExtension.finiteDimensionalAlgebraicClosureOfEssFiniteType`. -/
#check FieldExtension.existsFiniteTranscendenceBasisFiniteDimensionalOverAdjoin
#check FieldExtension.basisFieldLinearDisjointOfFiniteAlgebraic
@[stacks 037J]
#check FieldExtension.finiteDimensionalAlgebraicClosureOfEssFiniteType
