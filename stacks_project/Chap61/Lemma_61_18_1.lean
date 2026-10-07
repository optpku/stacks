module

public import stacks_project.Chap61.Lemma_61_18_1_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

/- Lemma 61.18.1 (1): the pro-étale site Sch_proétale has enough points. -/
@[stacks 0992] #check @hasEnoughPoints_proetale

/- Lemma 61.18.1 (2): the pro-étale site S_proétale has enough points. -/
@[stacks 0992] #check @ProEt.hasEnoughPoints

/- Lemma 61.18.1 (3): the pro-étale site (Sch/S)_proétale has enough points. -/
@[stacks 0992] #check @hasEnoughPoints_proetaleOver

/- Lemma 61.18.1 (4): the pro-étale site S_affine,proétale has enough points. -/
@[stacks 0992] #check @ProEt.hasEnoughPoints_affine

/- Lemma 61.18.1 (5): the pro-étale site (Aff/S)_proétale has enough points. -/
@[stacks 0992] #check @ChosenBigProetaleSite.hasEnoughPoints_bigAffine
