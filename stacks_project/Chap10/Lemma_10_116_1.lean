/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.FractionRing
import StacksCheckRecall

@[expose] public section

/-!
# Dimension and Generic Transcendence Degree

@stack 00P0
-/

@[stacks 00P0 "(1), global fraction-field dimension"]
#check @Algebra.FiniteType.ringKrullDim_eq_trdeg_fractionRing

@[stacks 00P0 "(2), maximal-local dimension"]
#check @Algebra.FiniteType.ringKrullDim_localizationAtMaximal_eq_trdeg_fractionRing

/- The algebra-level core before transport to the fraction field. -/
@[stacks 00P0 "algebra-level core"]
#check @Algebra.FiniteType.ringKrullDim_eq_trdeg
