/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Local
import StacksCheckRecall

@[expose] public section

/-!
# Local Nagata Criteria

@stack 0BI2

This chapter item is a source-facing recall of the shared local
analytic-unramifiedness criterion for Nagata rings.
-/

-- Lemma 10.162.14, tag `0BI2`: a Noetherian local ring is Nagata exactly when
-- finite domain algebras satisfy the analytic-unramifiedness local tests.
@[stacks 0BI2]
#check @NagataRing.local_tfae

@[stacks 0BI2 "finite local-domain analytic criterion"]
#check @NagataRing.of_finiteLocalDomain_analyticallyUnramified
