/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
import StacksCheckRecall

@[expose] public section

/-!
# Local Dimension of a Finite-Type Algebra

@stack 00OT
-/

/- Lemma 10.114.5 (1): local dimension is the supremum of the dimensions of the
irreducible components through the point. -/
@[stacks 00OT "(1), local dimension by irreducible components"]
#check @PrimeSpectrum.topologicalKrullDimAt_eq_iSup_irreducibleComponents_through

/- Lemma 10.114.5 (2): local dimension is the infimum of the dimensions of the
maximal localizations above the point. -/
@[stacks 00OT "(2), local dimension by maximal localizations"]
#check @PrimeSpectrum.topologicalKrullDimAt_eq_iInf_ringKrullDim_localizationAtMaximal_over
