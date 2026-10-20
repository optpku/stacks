/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Functor.StructuredArrow.Flat
import StacksCheckRecall

/-!
# Lemma 7.5.1

The finite-limit weak-cocone API for opposite structured-arrow categories is
owned by ReasLib. This file retains the source label as a thin recall.
-/

@[expose] public section

/- Lemma 7.5.1 (00X4): a pullback- and equalizer-preserving functor gives
`(StructuredArrow V u)ᵒᵖ` span cocones and parallel-pair cocones, the latter
being the formal version of postcomposition equalizers. -/
@[stacks 00X4] #check @CategoryTheory.StructuredArrow.Op.hasCocones

/- The two reusable weak-cocone owners remain available independently to
downstream filtered-colimit arguments. -/
#check @CategoryTheory.HasSpanCocones
#check @CategoryTheory.HasParallelPairCocones
