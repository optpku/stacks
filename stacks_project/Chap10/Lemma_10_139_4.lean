/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.Retraction
public import ReasLib.RingTheory.Smooth.Retraction.Completion
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.139.4

@stack 05D5
-/

/- Lemma 10.139.4 [stacks 05D5]: canonical recall of finite projectivity for the cotangent
module of a smooth algebra retraction.  Smoothness supplies the finite and projective Kahler
differential hypotheses of this more general retraction API. -/
@[stacks 05D5 "(1), finite projective conormal module"]
#check @KaehlerDifferential.Retraction.cotangent_finite_projective

/- Lemma 10.139.4 [stacks 05D5]: canonical recall of the formal-power-series description of a
formally smooth retraction completion with finite free conormal module. -/
@[stacks 05D5 "(2), power-series completion"]
#check @Algebra.FormallySmooth.Retraction.exists_adicCompletion_equiv_mvPowerSeries
