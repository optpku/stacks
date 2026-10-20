module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Unramified
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.112.9

The repository path retains the legacy numbering.  The current Stacks entry is Lemma 15.113.9,
tag `0EXS`.  Its integral-closure tower condition and branchwise composition theorem are owned by
`DVR.Field.IsUnramified`; this file is the source-facing recall surface.

@stack 0EXS
-/

/- Lemma 15.112.9 (local branch hypothesis): the intermediate-to-top unramified condition. -/
@[stacks 0EXS "Lemma 15.112.9: local branch hypothesis in the integral-closure tower"]
#check @DVR.Field.IsUnramified.IsUnramifiedOnTower

/- Lemma 15.112.9 (branch conclusion): compose the two local unramified branches. -/
@[stacks 0EXS "Lemma 15.112.9: branchwise unramifiedness composes"]
#check @DVR.Field.IsUnramified.atIntegralClosureTower

/- Lemma 15.112.9 (field conclusion): the finite separable tower remains unramified. -/
@[stacks 0EXS "Lemma 15.112.9: unramifiedness composes in a finite separable tower"]
#check @DVR.Field.IsUnramified.ofIntegralClosureTower
