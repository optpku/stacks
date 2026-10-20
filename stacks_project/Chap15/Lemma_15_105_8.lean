/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Weakly.AbsolutelyFlat
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.105.8 (092I)

@stack 092I

The shared owner keeps the tensor-square multiplication map explicit in part (1), and uses the
canonical `Algebra.WeaklyEtale` predicate for reducedness ascent in part (2).
-/

/- Lemma 15.105.8 (1): if `A` is absolutely flat and
`Algebra.tensorSquareMultiplication A B` is flat, then `B` is absolutely flat. -/
@[stacks 092I "Lemma 15.105.8 (1)"]
#check @IsAbsolutelyFlatRing.of_tensorSquareMultiplication_flat

/- Lemma 15.105.8 (2): reducedness ascends along a weakly etale map. -/
@[stacks 092I "Lemma 15.105.8 (2)"]
#check @Algebra.WeaklyEtale.isReduced

/- The owner-level specialization of part (1) to a weakly etale map. -/
#check @IsAbsolutelyFlatRing.of_weaklyEtale
