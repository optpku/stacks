/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.JacobiZariski
import StacksCheckRecall

/-!
@stack 065V
-/

@[expose] public section

/- Lemma 10.134.7 [stacks 065V] (1): canonical recall of the first
Jacobi-Zariski exactness map. -/

@[stacks 065V "(1)"]
#check @Algebra.H1Cotangent.exact_map_δ

/- Lemma 10.134.7 [stacks 065V] (2): canonical recall of surjectivity of the
connecting map when the outside algebra map is surjective. -/

@[stacks 065V "(2)"]
#check @Algebra.H1Cotangent.delta_surjective_of_algebraMap_surjective
