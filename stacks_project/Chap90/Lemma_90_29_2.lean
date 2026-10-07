module

public import stacks_project.Chap90.Lemma_90_29_2_Instances
public import stacks_project.Chap90.Lemma_90_29_2_IsoClass
import StacksCheckRecall

/-!
# Elementary properties of change of residue field

In Situation 90.29.1, fibrewise isomorphism classes commute with residue-field
reindexing, and predeformation, (S1), (S2), and (RS) pass from `p` to
`residueChangeOver p`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat

/- Lemma 90.29.2 (1): `fiberIsoClassFunctor (residueChangeOver p)` identifies with
`fiberIsoClassFunctor p` after `residueChangeFunctor`. -/
@[stacks 07WA]
#check residueChangeOver.isoClassEquiv

/- Lemma 90.29.2 (2): if `p` is a predeformation category, then so is
`residueChangeOver p`. -/
@[stacks 07WA]
#check residueChangeOver.instIsPredeformationCategory

/- Lemma 90.29.2 (3): if `p` satisfies (S1), then so does `residueChangeOver p`. -/
@[stacks 07WA]
#check residueChangeOver.instHasSchlessingerS1

/- Lemma 90.29.2 (4): if `p` satisfies (S2), then so does `residueChangeOver p`. -/
@[stacks 07WA]
#check residueChangeOver.instHasSchlessingerS2

/- Lemma 90.29.2 (5): if `p` satisfies (RS), then so does `residueChangeOver p`. -/
@[stacks 07WA]
#check residueChangeOver.instHasRimSchlessinger
