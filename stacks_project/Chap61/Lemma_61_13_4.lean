/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_13_4_Enough
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

/- Lemma 61.13.4 (1): the pro-étale site S_proétale has enough affine
quasi-compact weakly contractible objects. -/
@[stacks 0990] #check @ProEt.hasEnough_isAffine_isWeaklyContractible

/- Lemma 61.13.4 (2): the pro-étale site (Sch/S)_proétale has enough affine
quasi-compact weakly contractible objects. -/
@[stacks 0990] #check @hasEnough_isAffine_isWeaklyContractible_proetaleOver

/- Lemma 61.13.4 (3): the pro-étale site S_affine,proétale has enough weakly
contractible objects. -/
@[stacks 0990] #check @ProEt.hasEnough_isWeaklyContractible_affine

/- Lemma 61.13.4 (4): the pro-étale site (Aff/S)_proétale has enough weakly
contractible objects. -/
@[stacks 0990] #check @ChosenBigProetaleSite.hasEnough_isWeaklyContractible_bigAffine

/- Lemma 61.13.4 (5): if S is affine, the pro-étale site S_app has enough
weakly contractible objects. -/
@[stacks 0990] #check @ProEt.hasEnough_isWeaklyContractible_affineIndEtale
