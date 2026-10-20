/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.BoundedAbove

/-!
# Lemma 15.59.7

@stack 064K

The reusable ModuleCat specialization is
`CochainComplex.isKFlat_of_boundedAbove_of_flat`; its categorical core is
`HomologicalComplex.IsTermwiseFlat.isKFlat_of_boundedAbove`.
-/

@[expose] public section

/- Lemma 15.59.7 (064K): a bounded-above complex of flat modules is K-flat. -/
@[stacks 064K "bounded-above complexes of flat modules are K-flat"]
#check @CochainComplex.isKFlat_of_boundedAbove_of_flat

#check @HomologicalComplex.IsTermwiseFlat.isKFlat_of_boundedAbove
