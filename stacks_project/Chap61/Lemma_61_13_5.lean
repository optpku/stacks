/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_13_5_Cover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 61.13.5 (1): the pro-étale site Sch_proétale has, for any object U,
a covering {V ⟶ U} with V a weakly contractible object. -/
@[stacks 0F4P] #check Proetale.exists_coveringArrow_isWeaklyContractible

/- Lemma 61.13.5 (2): the pro-étale site S_proétale has, for any object U,
a covering {V ⟶ U} with V a weakly contractible object. -/
@[stacks 0F4P] #check ProEt.exists_coveringArrow_isWeaklyContractible

/- Lemma 61.13.5 (3): the pro-étale site (Sch/S)_proétale has, for any object U,
a covering {V ⟶ U} with V a weakly contractible object. -/
@[stacks 0F4P] #check Proetale.exists_coveringArrow_isWeaklyContractible_over

/- Lemma 61.13.5 (4): if U is quasi-compact in Sch_proétale, the covering object
V may be chosen affine and weakly contractible. -/
@[stacks 0F4P] #check Proetale.exists_coveringArrow_isAffine_isWeaklyContractible

/- Lemma 61.13.5 (5): if U is quasi-compact in S_proétale, the covering object
V may be chosen affine and weakly contractible. -/
@[stacks 0F4P] #check ProEt.exists_coveringArrow_isAffine_isWeaklyContractible

/- Lemma 61.13.5 (6): if U is quasi-compact in (Sch/S)_proétale, the covering
object V may be chosen affine and weakly contractible. -/
@[stacks 0F4P] #check Proetale.exists_coveringArrow_isAffine_isWeaklyContractible_over
