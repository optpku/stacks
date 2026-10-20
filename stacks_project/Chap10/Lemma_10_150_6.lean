module

public import ReasLib.RingTheory.RingHom.FormallyEtale.QuotientPow
public import ReasLib.RingTheory.RingHom.FormallyEtale.AssociatedGraded
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.150.6

@stack 0H1D

The source statements are canonical recalls.  The reusable owners are
`RingHom.FormallyEtale.quotientMap_pow_bijective`, its degreewise companion
`RingHom.FormallyEtale.associatedGradedGrade_bijective`, and
`RingHom.FormallyEtale.associatedGradedMap_bijective`.
-/

/- Lemma 10.150.6 (1): formally etale quotient maps are bijective on every
power of the target ideal. -/
@[stacks 0H1D "(1)"]
#check @RingHom.FormallyEtale.quotientMap_pow_bijective

/- Lemma 10.150.6 (1), degreewise associated-graded form. -/
@[stacks 0H1D "(1), degreewise"]
#check @RingHom.FormallyEtale.associatedGradedGrade_bijective

/- Lemma 10.150.6 (2): the induced associated-graded ring map is bijective. -/
@[stacks 0H1D "(2)"]
#check @RingHom.FormallyEtale.associatedGradedMap_bijective
