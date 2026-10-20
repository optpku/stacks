/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Compactness.Compact
import StacksCheckRecall

@[expose] public section

/-
`generalized_tube_lemma` has exactly the source-facing open-set formulation. The stronger filter
identity `IsCompact.nhdsSet_prod_eq` is its canonical core, while `generalized_tube_lemma'` is a
relative-neighborhood variant. Using the exact theorem avoids a parallel wrapper: it retains
precisely arbitrary topological spaces, compact subsets `A` and `B`, and an open superset of
`A ×ˢ B`, while exposing mathlib's canonical result directly for downstream use.
-/

/- Lemma 5.17.1 (Tube lemma): let `A ⊆ X` and `B ⊆ Y` be quasi-compact subsets and let
`A ×ˢ B ⊆ W ⊆ X × Y` with `W` open. Then there exist open neighborhoods `U` of `A` and `V` of
`B` such that `U ×ˢ V ⊆ W`. This is exactly the canonical mathlib theorem
`generalized_tube_lemma`, so the source-facing item should expose that theorem directly rather
than add a parallel local wrapper. -/
@[stacks 005N "open product neighborhoods of quasi-compact subsets"]
#check generalized_tube_lemma
