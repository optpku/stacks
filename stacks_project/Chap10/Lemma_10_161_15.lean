/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Nagata.LocalN1
import StacksCheckRecall

@[expose] public section

/-!
# Local N-1 Criteria
@stack 0333

The reusable `N-1` locality criteria are owned by ReasLib; this chapter file
keeps the textbook entry points.
-/

-- Lemma 10.161.15 (1), tag `0333`: an `N-1` domain has a nonzero normal
-- principal-open localization.
@[stacks 0333 "(1)"]
#check @IsN1Ring.exists_normal_localizationAway

-- Lemma 10.161.15 (2), tag `0333`: an `N-1` domain is `N-1` at each maximal
-- localization.
@[stacks 0333 "(2)"]
#check @IsN1Ring.atMaximal

-- Lemma 10.161.15 (3), tag `0333`: normality on a nonzero principal open and
-- `N-1` at every maximal localization imply `N-1`.
@[stacks 0333 "(3)"]
#check @IsN1Ring.of_normal_localizationAway_of_forall_atMaximal
