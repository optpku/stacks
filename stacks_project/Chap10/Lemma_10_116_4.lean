/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.Surjective
import StacksCheckRecall

/-!
# Local Dimension Under a Surjective Presentation

@stack 00P2
-/

/- Lemma 10.116.4: a surjective finite-type presentation changes local
dimension by its prime-height defect. -/
@[stacks 00P2]
#check @PrimeSpectrum.topologicalKrullDimAt_comap_eq_add_primeHeightDefect
