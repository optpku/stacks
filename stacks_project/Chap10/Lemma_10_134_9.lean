/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.DirectLimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.134.9

@stack 07BQ

The filtered direct-limit construction and its comparison with the canonical
naive cotangent complex are owned by `Algebra.NaiveCotangent.DirectLimit`.
This chapter file records the source statement without rebuilding its
presentation-level proof infrastructure.
-/

/- Lemma 10.134.9 [stacks 07BQ]: for a directed system of ring maps
`R i → S i`, the canonical comparison from the filtered direct-limit model of
the stagewise naive cotangent complexes `NL{S i⁄R i}` to
`NL{colim S⁄colim R}` is an isomorphism.  The owner exposes the component
diagram, its canonical comparison, and the resulting H1 criterion separately
for downstream use. -/
@[stacks 07BQ "canonical direct-limit comparison"]
#check @Algebra.NaiveCotangent.DirectLimit.comparison

@[stacks 07BQ "direct-limit comparison is an isomorphism"]
#check @Algebra.NaiveCotangent.DirectLimit.comparison_isIso

@[stacks 07BQ "canonical direct-limit comparison isomorphism"]
#check @Algebra.NaiveCotangent.DirectLimit.comparisonIso

@[stacks 07BQ "comparison isomorphism forward map"]
#check @Algebra.NaiveCotangent.DirectLimit.comparisonIso_hom

@[stacks 07BQ "comparison isomorphism inverse map"]
#check @Algebra.NaiveCotangent.DirectLimit.comparisonIso_inv

@[stacks 07BQ "direct-limit naive cotangent target"]
#check @Algebra.NaiveCotangent.DirectLimit.targetComplex

@[stacks 07BQ "direct-limit naive cotangent model"]
#check @Algebra.NaiveCotangent.DirectLimit.Model.complex
@[stacks 07BQ "direct-limit algebra map"]
#check @Algebra.NaiveCotangent.DirectLimit.limitHom
@[stacks 07BQ "direct-limit algebra map on stages"]
#check @Ring.DirectLimit.Algebra.map_comp_of
@[stacks 07BQ "direct-limit stage component"]
#check @Algebra.NaiveCotangent.DirectLimit.Stage.component
@[stacks 07BQ "direct-limit stage component map"]
#check @Algebra.NaiveCotangent.DirectLimit.Stage.componentMap
@[stacks 07BQ "direct-limit naive cotangent model component"]
#check @Algebra.NaiveCotangent.DirectLimit.Model.component
@[stacks 07BQ "direct-limit comparison component"]
#check @Algebra.NaiveCotangent.DirectLimit.Comparison.component
@[stacks 07BQ "degree-zero direct-limit comparison component"]
#check @Algebra.NaiveCotangent.DirectLimit.Comparison.zero
@[stacks 07BQ "degree-one direct-limit comparison component"]
#check @Algebra.NaiveCotangent.DirectLimit.Comparison.one
@[stacks 07BQ "higher direct-limit comparison components"]
#check @Algebra.NaiveCotangent.DirectLimit.Comparison.succ
@[stacks 07BQ "direct-limit cotangent H1"]
#check @Algebra.NaiveCotangent.DirectLimit.H1.subsingleton_of_stagewise_injective
