/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Henselization.Comparison
import StacksCheckRecall

@[expose] public section

/-!
# Local comparisons of henselizations

Lemma 10.155.6 is a specialization of the universal property of a chosen
henselization.  ReasLib exposes existence and uniqueness propositionally;
downstream proofs take a comparison map explicitly instead of relying on a
globally selected `Classical.choose` witness.

@stack 04GS
-/

/- Lemma 10.155.6, tag `04GS`: a henselization has a unique local algebra
map to every henselian local algebra over its base, in particular to a
henselization reached along a local map. -/
@[stacks 04GS]
#check @IsHenselizationOf.existsUnique_lift
#check @IsHenselizationOf.local_nonempty
#check @IsHenselizationOf.local_subsingleton
#check @IsHenselizationOf.local_eq
