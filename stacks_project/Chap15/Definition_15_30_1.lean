/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Homology.First.Comparison

@[expose] public section

/-!
# Koszul regularity

The module-valued and ring-valued regularity predicates belong to the neutral
`RingTheory.Sequence` API; this chapter entry is a source-facing recall.

@stack 062E
-/

/- Definition 15.30.1 (Stacks tag `062E`): finite-family Koszul regularity is owned by the neutral predicates
`RingTheory.Sequence.IsKoszulRegularOn`, `RingTheory.Sequence.IsH1RegularOn`,
`RingTheory.Sequence.IsKoszulRegularSequence`, and `RingTheory.Sequence.IsH1RegularSequence`. -/
@[stacks 062E "Definition 15.30.1 (1), module Koszul-regular families"]
#check @RingTheory.Sequence.IsKoszulRegularOn

@[stacks 062E "Definition 15.30.1 (2), module H1-regular families"]
#check @RingTheory.Sequence.IsH1RegularOn

@[stacks 062E "Definition 15.30.1 (3), Koszul-regular families"]
#check @RingTheory.Sequence.IsKoszulRegularSequence

@[stacks 062E "Definition 15.30.1 (4), H1-regular families"]
#check @RingTheory.Sequence.IsH1RegularSequence

#check @KoszulComplex.Homology.H1.Comparison.comparison
#check @KoszulComplex.Homology.H1.Comparison.comparison_isIso
#check @KoszulComplex.Homology.H1.isH1RegularOn_iff_isZero
