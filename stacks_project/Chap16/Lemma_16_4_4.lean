module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.NeronBlowup.SmoothnessCriterion

@[expose] public section

/- Lemma 16.4.4 (tag 0BJ5): the canonical Kähler-module criterion and its
source-faithful surjective-presentation form are provided by ReasLib. -/

@[stacks 0BJ5]
#check @Algebra.DVR.Factorization.ClosedCenter.smooth_of_kaehler

@[stacks 0BJ5]
#check @Algebra.DVR.Factorization.ClosedCenter.smooth_of_presentation

@[stacks 0BJ5]
#check @AlgHom.SurjectivePresentation.conormalBaseChangeMap

@[stacks 0BJ5]
#check @AlgHom.SurjectivePresentation.ConormalCokernel

@[stacks 0BJ5]
#check @AlgHom.SurjectivePresentation.kaehlerBaseChangeEquiv

@[stacks 0BJ5]
#check @AlgHom.SurjectivePresentation.conormalCokernel_free_iff
